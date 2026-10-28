-- Prove2me | solution 1 for ChanceStateCtrl.General.clarke_chain_rule_neg_log
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:20:16.698109+00:00
-- url     : https://prove2.me/submissions/7f9e5ccd-4e04-4f3f-a158-873983549cf6

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Pointwise

namespace A3S48CR

lemma bdd_of_abs {α : Type*} {F : Filter α} [NeBot F] {A : α → ℝ} {M : ℝ}
    (hA : ∀ᶠ x in F, |A x| ≤ M) :
    F.IsBoundedUnder (· ≤ ·) A ∧ F.IsCoboundedUnder (· ≤ ·) A :=
  ⟨isBoundedUnder_of_eventually_le (a := M) (by filter_upwards [hA] with x hx using le_of_abs_le hx),
   isCoboundedUnder_le_of_eventually_le F (x := -M)
    (by filter_upwards [hA] with x hx using neg_le_of_abs_le hx)⟩

lemma close_le {α : Type*} {F : Filter α} [NeBot F] {A B : α → ℝ} {M : ℝ}
    (hA : ∀ᶠ x in F, |A x| ≤ M) (hB : ∀ᶠ x in F, |B x| ≤ M)
    (h : ∀ ε > 0, ∀ᶠ x in F, A x ≤ B x + ε) : limsup A F ≤ limsup B F := by
  obtain ⟨_, cA⟩ := bdd_of_abs hA
  obtain ⟨bB, cB⟩ := bdd_of_abs hB
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbB' : F.IsBoundedUnder (· ≤ ·) (fun x => B x + ε) := by
    refine isBoundedUnder_of_eventually_le (a := M + ε) ?_
    filter_upwards [hB] with x hx using by linarith [le_of_abs_le hx]
  calc limsup A F ≤ limsup (fun x => B x + ε) F := limsup_le_limsup (h ε hε) cA hbB'
    _ = limsup B F + ε :=
      (Monotone.map_limsup_of_continuousAt (f := fun y : ℝ => y + ε)
        (fun _ _ h => by simpa using h) B (by fun_prop) bB cB).symm

lemma lim_eq {α : Type*} {F : Filter α} [NeBot F] {A B : α → ℝ} {M : ℝ}
    (hA : ∀ᶠ x in F, |A x| ≤ M) (hB : ∀ᶠ x in F, |B x| ≤ M)
    (h : ∀ ε > 0, ∀ᶠ x in F, |A x - B x| ≤ ε) : limsup A F = limsup B F :=
  le_antisymm
    (close_le hA hB fun ε hε => by
      filter_upwards [h ε hε] with x hx using by linarith [le_of_abs_le hx])
    (close_le hB hA fun ε hε => by
      filter_upwards [h ε hε] with x hx using by linarith [neg_le_of_abs_le hx])

end A3S48CR

open A3S48CR in
theorem solution {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (φ : U → ℝ) (us : U) (hφ_lip : ChanceStateCtrl.General.LocLipAt φ us) (hφ_pos : 0 < φ us)
    (p : ℝ) (hp : 0 < p) :
    ChanceStateCtrl.General.clarkeSubdiff (fun u => -Real.log (φ u) + Real.log p) us =
      (-(φ us)⁻¹) • ChanceStateCtrl.General.clarkeSubdiff φ us := by
  obtain ⟨K, T, hT, hK⟩ := hφ_lip
  set c := (φ us)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 hφ_pos
  set F : Filter (U × ℝ) := 𝓝 us ×ˢ 𝓝[>] (0:ℝ) with hF
  have hlim1 : ∀ h : U, Tendsto (fun q : U × ℝ => q.1 + q.2 • h) F (𝓝 us) := by
    intro h
    have hcont : Continuous (fun q : U × ℝ => q.1 + q.2 • h) := by fun_prop
    have := hcont.tendsto (us, 0)
    simp only [zero_smul, add_zero] at this
    refine this.mono_left ?_
    rw [hF, nhds_prod_eq]
    exact Filter.prod_mono le_rfl nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun q : U × ℝ => q.1) F (𝓝 us) := tendsto_fst
  have hpos : ∀ᶠ q in F, 0 < q.2 :=
    (tendsto_snd (f := 𝓝 us)).eventually self_mem_nhdsWithin
  have hσ : ∀ h : U, Tendsto (fun q : U × ℝ => (q.1 + q.2 • h, q.2)) F F :=
    fun h => (hlim1 h).prodMk (tendsto_snd (f := 𝓝 us))
  have hmap : ∀ h : U, map (fun q : U × ℝ => (q.1 + q.2 • h, q.2)) F = F := by
    intro h
    refine le_antisymm (hσ h) ?_
    calc F = map (fun q : U × ℝ => (q.1 + q.2 • h, q.2))
          (map (fun q : U × ℝ => (q.1 + q.2 • (-h), q.2)) F) := by
            rw [Filter.map_map]
            conv_lhs => rw [← Filter.map_id (f := F)]
            congr 1
            funext q; simp [smul_neg]
      _ ≤ _ := Filter.map_mono (hσ (-h))
  have hφc : ContinuousAt φ us := hK.continuousOn.continuousAt hT
  -- the key identity of Clarke directional derivatives
  have key : ∀ h : U, ChanceStateCtrl.General.clarkeDir (fun u => -Real.log (φ u) + Real.log p) us h
      = c * ChanceStateCtrl.General.clarkeDir φ us (-h) := by
    intro h
    unfold ChanceStateCtrl.General.clarkeDir
    set D : U × ℝ → ℝ := fun q => (φ q.1 - φ (q.1 + q.2 • h)) / q.2 with hD
    have hDG : D = (fun q : U × ℝ => (φ (q.1 + q.2 • (-h)) - φ q.1) / q.2) ∘
        (fun q : U × ℝ => (q.1 + q.2 • h, q.2)) := by
      funext q; simp [hD, smul_neg]
    set M : ℝ := K * ‖h‖ + 1 with hM
    have hM0 : 0 < M := by positivity
    have hDb : ∀ᶠ q in F, |D q| ≤ M := by
      filter_upwards [hlim0.eventually hT, (hlim1 h).eventually hT, hpos] with q h1 h2 h3
      have := hK.dist_le_mul _ h1 _ h2
      rw [Real.dist_eq, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos h3] at this
      simp only [hD]
      rw [abs_div, abs_of_pos h3, div_le_iff₀ h3]
      nlinarith
    have hφa : Tendsto (fun q : U × ℝ => φ q.1) F (𝓝 (φ us)) := hφc.tendsto.comp hlim0
    have hφb : Tendsto (fun q : U × ℝ => φ (q.1 + q.2 • h)) F (𝓝 (φ us)) :=
      hφc.tendsto.comp (hlim1 h)
    have hapos : ∀ᶠ q in F, 0 < φ q.1 := hφa.eventually (lt_mem_nhds hφ_pos)
    have hbpos : ∀ᶠ q in F, 0 < φ (q.1 + q.2 • h) := hφb.eventually (lt_mem_nhds hφ_pos)
    have hia := hφa.inv₀ hφ_pos.ne'
    have hib := hφb.inv₀ hφ_pos.ne'
    have hclose : ∀ ε > 0, ∀ᶠ q in F,
        |(-Real.log (φ (q.1 + q.2 • h)) + Real.log p - (-Real.log (φ q.1) + Real.log p)) / q.2
          - c * D q| ≤ ε := by
      intro ε hε
      have hδ : 0 < ε / M := by positivity
      filter_upwards [hDb, hapos, hbpos, hpos, hia.eventually (Metric.ball_mem_nhds _ hδ),
        hib.eventually (Metric.ball_mem_nhds _ hδ)] with q hq1 ha hb ht hia' hib'
      set a := φ q.1
      set b := φ (q.1 + q.2 • h)
      rw [Real.dist_eq] at hia' hib'
      have hX1 : Real.log a - Real.log b ≤ (a - b) * b⁻¹ := by
        have := Real.log_le_sub_one_of_pos (div_pos ha hb)
        rw [Real.log_div ha.ne' hb.ne'] at this
        have e : a / b - 1 = (a - b) * b⁻¹ := by field_simp
        linarith
      have hX2 : (a - b) * a⁻¹ ≤ Real.log a - Real.log b := by
        have := Real.log_le_sub_one_of_pos (div_pos hb ha)
        rw [Real.log_div hb.ne' ha.ne'] at this
        have e : b / a - 1 = -((a - b) * a⁻¹) := by field_simp; ring
        linarith
      have e1 : |(a - b) * (a⁻¹ - c)| ≤ |a - b| * (ε / M) := by
        rw [abs_mul]; gcongr
      have e2 : |(a - b) * (b⁻¹ - c)| ≤ |a - b| * (ε / M) := by
        rw [abs_mul]; gcongr
      have hXc : |Real.log a - Real.log b - c * (a - b)| ≤ |a - b| * (ε / M) := by
        rw [abs_le]
        constructor
        · have := (abs_le.1 e1).1; nlinarith
        · have := (abs_le.1 e2).2; nlinarith
      have hrw : (-Real.log b + Real.log p - (-Real.log a + Real.log p)) / q.2 - c * D q
          = (Real.log a - Real.log b - c * (a - b)) / q.2 := by
        simp only [hD]; field_simp; ring
      rw [hrw, abs_div, abs_of_pos ht, div_le_iff₀ ht]
      have hDq : |a - b| = |D q| * q.2 := by
        simp only [hD]; rw [abs_div, abs_of_pos ht, div_mul_cancel₀ _ ht.ne']
      calc |Real.log a - Real.log b - c * (a - b)| ≤ |a - b| * (ε / M) := hXc
        _ = |D q| * (ε / M) * q.2 := by rw [hDq]; ring
        _ ≤ M * (ε / M) * q.2 := by gcongr
        _ = ε * q.2 := by field_simp
    have hcDb : ∀ᶠ q in F, |c * D q| ≤ c * M := by
      filter_upwards [hDb] with q hq
      rw [abs_mul, abs_of_pos hc0]; gcongr
    have hAb : ∀ᶠ q in F, |(-Real.log (φ (q.1 + q.2 • h)) + Real.log p
        - (-Real.log (φ q.1) + Real.log p)) / q.2| ≤ c * M + 1 := by
      filter_upwards [hclose 1 one_pos, hcDb] with q h1 h2
      calc _ = |(_ - c * D q) + c * D q| := by ring_nf
        _ ≤ |_ - c * D q| + |c * D q| := abs_add_le _ _
        _ ≤ 1 + c * M := add_le_add h1 h2
        _ = c * M + 1 := by ring
    have hcDb' : ∀ᶠ q in F, |c * D q| ≤ c * M + 1 := by
      filter_upwards [hcDb] with q hq using by linarith
    rw [lim_eq hAb hcDb' hclose]
    obtain ⟨bD, cD⟩ := bdd_of_abs hDb
    have hmono := Monotone.map_limsup_of_continuousAt (f := fun y : ℝ => c * y)
      (fun _ _ h => mul_le_mul_of_nonneg_left h hc0.le) D (by fun_prop) bD cD
    simp only [Function.comp_def] at hmono
    rw [← hmono]
    congr 1
    rw [hDG, Filter.limsup_comp, hmap h]
  ext x
  simp only [ChanceStateCtrl.General.clarkeSubdiff, Set.mem_smul_set, Set.mem_setOf_eq, key]
  constructor
  · intro hx
    refine ⟨(-c)⁻¹ • x, fun h => ?_, ?_⟩
    · have := hx (-h)
      rw [neg_neg, map_neg] at this
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, inv_neg, neg_mul]
      calc -(c⁻¹ * x h) = c⁻¹ * (-x h) := by ring
        _ ≤ c⁻¹ * (c * ChanceStateCtrl.General.clarkeDir φ us h) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hc0.le)
        _ = ChanceStateCtrl.General.clarkeDir φ us h := inv_mul_cancel_left₀ hc0.ne' _
    · rw [smul_smul, mul_inv_cancel₀ (neg_ne_zero.2 hc0.ne'), one_smul]
  · rintro ⟨y, hy, rfl⟩ h
    have := hy (-h)
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_neg] at this ⊢
    nlinarith
