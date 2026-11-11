-- Prove2me | solution 1 for EthierKurtz.martingale_solution_is_markov
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T23:46:24.585829+00:00
-- url     : https://prove2.me/submissions/8af4d6c2-9b5d-415b-970b-b337cf25dfc7

import Mathlib
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

set_option autoImplicit false

open MeasureTheory Filter TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace P54176b4e

/-! ## C4: Laplace uniqueness for bounded continuous functions on `[0, ∞)` -/

lemma chi_cont {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ici 0)) {C : ℝ}
    (hb : ∀ s, 0 ≤ s → |φ s| ≤ C) :
    ContinuousOn (fun x : ℝ => x * φ (-Real.log x)) (Icc 0 1) := by
  have hmaps : MapsTo (fun y : ℝ => -Real.log y) (Icc 0 1) (Ici 0) := by
    intro y hy
    simp only [mem_Ici, Left.nonneg_neg_iff]
    exact Real.log_nonpos hy.1 hy.2
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · subst h0
    rw [ContinuousWithinAt, show (0:ℝ) * φ (-Real.log 0) = 0 by simp]
    refine squeeze_zero_norm' (a := fun y : ℝ => |y| * C) ?_ ?_
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb _ (hmaps hy)) (abs_nonneg _)
    · have : Tendsto (fun y : ℝ => |y| * C) (𝓝 0) (𝓝 (|0| * C)) :=
        ((continuous_abs.mul continuous_const).tendsto 0)
      simp only [abs_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
  · have hl : ContinuousWithinAt (fun y : ℝ => -Real.log y) (Icc 0 1) x :=
      (Real.continuousAt_log hpos.ne').neg.continuousWithinAt
    exact continuousWithinAt_id.mul
      (ContinuousWithinAt.comp (f := fun y : ℝ => -Real.log y) (hc _ (hmaps hx)) hl hmaps)

lemma integrableOn_exp_mul {k : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hk : AEStronglyMeasurable k (volume.restrict (Ioi (0:ℝ)))) {K : ℝ}
    (hK : ∀ s, 0 < s → |k s| ≤ K) :
    IntegrableOn (fun s => Real.exp (-b * s) * k s) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hb).mul_const K) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hk
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
    exact mul_le_mul_of_nonneg_left (hK s hs) (Real.exp_pos _).le

/-- Laplace transforms at the integers `1, 2, 3, ...` determine a bounded continuous function. -/
lemma laplace_unique {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ici 0)) {C : ℝ}
    (hb : ∀ s, 0 ≤ s → |φ s| ≤ C)
    (hL : ∀ n : ℕ, ∫ s in Ioi (0:ℝ), Real.exp (-((n:ℝ) + 1) * s) * φ s = 0) :
    ∀ s, 0 ≤ s → φ s = 0 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0 le_rfl)
  have hmeas : AEStronglyMeasurable φ (volume.restrict (Ioi (0:ℝ))) :=
    (hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hb' : ∀ s, 0 < s → |φ s| ≤ C := fun s hs => hb s hs.le
  -- polynomial test functions
  have hpoly : ∀ p : Polynomial ℝ,
      ∫ s in Ioi (0:ℝ), Real.exp (-s) * (p.eval (Real.exp (-s)) * φ s) = 0 := by
    intro p
    have he : ∀ (s : ℝ) (i : ℕ),
        Real.exp (-s) * Real.exp (-s) ^ i = Real.exp (-((i:ℝ) + 1) * s) := by
      intro s i
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have hsum : ∀ s : ℝ, Real.exp (-s) * (p.eval (Real.exp (-s)) * φ s) =
        ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (Real.exp (-((i:ℝ) + 1) * s) * φ s) := by
      intro s
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he s i]; ring
    simp_rw [hsum]
    rw [integral_finsetSum _ (fun i _ =>
      (integrableOn_exp_mul (by positivity) hmeas hb').const_mul _)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, hL i, mul_zero]
  -- the key integral vanishes
  set g : ℝ → ℝ := fun s => Real.exp (-s) * (Real.exp (-s) * φ s * φ s) with hg
  have hgint : IntegrableOn g (Ioi 0) := by
    have := integrableOn_exp_mul (b := 1) one_pos
      (k := fun s => Real.exp (-s) * φ s * φ s)
      ((Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.mul hmeas |>.mul hmeas)
      (K := C * C) (fun s hs => by
        show |Real.exp (-s) * φ s * φ s| ≤ C * C
        rw [abs_mul, abs_mul, Real.abs_exp]
        have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have := hb' s hs
        calc Real.exp (-s) * |φ s| * |φ s| ≤ 1 * C * C := by
              gcongr
          _ = C * C := by ring)
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [hg, neg_mul, one_mul]
  have hgnn : ∀ s, 0 ≤ g s := fun s => by
    simp only [hg]
    exact mul_nonneg (Real.exp_pos _).le
      (by rw [mul_assoc]; exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _))
  have hI : ∫ s in Ioi (0:ℝ), g s = 0 := by
    refine le_antisymm ?_ (setIntegral_nonneg measurableSet_Ioi fun s _ => hgnn s)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < ε / (C + 1) := by positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1
      (fun x : ℝ => x * φ (-Real.log x)) (chi_cont hc hb) (ε / (C + 1)) hε'
    have hdiff : ∫ s in Ioi (0:ℝ), g s = ∫ s in Ioi (0:ℝ),
        Real.exp (-s) * ((Real.exp (-s) * φ (-Real.log (Real.exp (-s)))
          - p.eval (Real.exp (-s))) * φ s) := by
      have hpi : IntegrableOn (fun s => Real.exp (-s) * (p.eval (Real.exp (-s)) * φ s)) (Ioi 0) := by
        obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, |p.eval x| ≤ M :=
          ⟨_, fun x hx => (isCompact_Icc.exists_bound_of_continuousOn
            (p.continuous.continuousOn)).choose_spec x hx⟩
        have := integrableOn_exp_mul (b := 1) one_pos
          (k := fun s => p.eval (Real.exp (-s)) * φ s)
          ((p.continuous.comp (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable.mul
            hmeas) (K := M * C) (fun s hs => by
            show |p.eval (Real.exp (-s)) * φ s| ≤ M * C
            rw [abs_mul]
            have hx : Real.exp (-s) ∈ Icc (0:ℝ) 1 :=
              ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
            exact mul_le_mul (hM _ hx) (hb' s hs) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hM _ hx)))
        refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
        simp only [neg_mul, one_mul]
      have h0 := hpoly p
      rw [show (∫ s in Ioi (0:ℝ), g s) = (∫ s in Ioi (0:ℝ), g s) - ∫ s in Ioi (0:ℝ),
          Real.exp (-s) * (p.eval (Real.exp (-s)) * φ s) by rw [h0, sub_zero],
        ← integral_sub hgint hpi]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      simp only [hg, Real.log_exp, neg_neg]; ring
    rw [hdiff]
    have hbound : ∀ s ∈ Ioi (0:ℝ), ‖Real.exp (-s) * ((Real.exp (-s) * φ (-Real.log (Real.exp (-s)))
          - p.eval (Real.exp (-s))) * φ s)‖ ≤ Real.exp (-s) * (ε / (C + 1) * C) := by
      intro s hs
      have hx : Real.exp (-s) ∈ Icc (0:ℝ) 1 :=
        ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by simp only [mem_Ioi] at hs; linarith)⟩
      have h1 := hp _ hx
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, abs_sub_comm]
      gcongr
      all_goals first | exact h1.le | exact hb' s hs
    calc ∫ s in Ioi (0:ℝ), Real.exp (-s) * ((Real.exp (-s) * φ (-Real.log (Real.exp (-s)))
          - p.eval (Real.exp (-s))) * φ s)
        ≤ ‖∫ s in Ioi (0:ℝ), Real.exp (-s) * ((Real.exp (-s) * φ (-Real.log (Real.exp (-s)))
          - p.eval (Real.exp (-s))) * φ s)‖ := Real.le_norm_self _
      _ ≤ ∫ s in Ioi (0:ℝ), Real.exp (-s) * (ε / (C + 1) * C) :=
          norm_integral_le_of_norm_le
            (by simpa using (exp_neg_integrableOn_Ioi 0 one_pos).mul_const (ε / (C + 1) * C))
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))
      _ = ε / (C + 1) * C := by rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]
      _ ≤ 0 + ε := by
          rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  -- conclude
  have hae : g =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hgnn) hgint).1 hI
  have hgc : ContinuousOn g (Ioi 0) := by
    have hφ := hc.mono Ioi_subset_Ici_self
    simp only [hg]
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.mul
      (((Real.continuous_exp.comp continuous_neg).continuousOn.mul hφ).mul hφ)
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hgc continuousOn_const
  have hpos : ∀ s, 0 < s → φ s = 0 := by
    intro s hs
    have h := heq hs
    simp only [hg, Pi.zero_apply] at h
    have h1 := Real.exp_pos (-s)
    have : φ s * φ s = 0 := by
      have : Real.exp (-s) * Real.exp (-s) * (φ s * φ s) = 0 := by rw [← h]; ring
      rcases mul_eq_zero.1 this with h2 | h2
      · exact absurd h2 (by positivity)
      · exact h2
    exact mul_self_eq_zero.1 this
  intro s hs
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    have h1 : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) :=
      (hc 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
    have h2 : Tendsto φ (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hpos s hs).symm)
    exact tendsto_nhds_unique h1 h2
  · exact hpos s h0

end P54176b4e

namespace P54176b4eR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section relation

variable (A : Submodule ℝ (E × E))

/-- Dissipativity of a linear relation. -/
def Diss : Prop := ∀ fg ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖

variable {A}

lemma diss_zero (hA : Diss A) {l : ℝ} (hl : 0 < l) {f g : E} (h : (f, g) ∈ A)
    (h0 : l • f - g = 0) : f = 0 := by
  have := hA (f, g) h l hl
  simp only [h0, norm_zero] at this
  have : ‖f‖ ≤ 0 := by nlinarith [norm_nonneg f]
  exact norm_le_zero_iff.mp this

/-- Step 1: dense range of `l - A` is full range, for closed dissipative `A`. -/
lemma range_full [CompleteSpace E] (hcl : IsClosed (A : Set (E × E))) (hA : Diss A) {l : ℝ}
    (hl : 0 < l) (hr : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖(l • fg.1 - fg.2) - h‖ < δ)
    (h : E) : ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  have hex : ∀ k : ℕ, ∃ fg ∈ A, ‖(l • fg.1 - fg.2) - h‖ < 1 / ((k : ℝ) + 1) :=
    fun k => hr h _ (by positivity)
  choose p hpA hpn using hex
  have hcau : ∀ m k : ℕ, ‖(p m).1 - (p k).1‖ ≤ l⁻¹ * (1 / ((m : ℝ) + 1) + 1 / ((k : ℝ) + 1)) := by
    intro m k
    have hd := hA (p m - p k) (A.sub_mem (hpA m) (hpA k)) l hl
    simp only [Prod.fst_sub, Prod.snd_sub] at hd
    have e : l • ((p m).1 - (p k).1) - ((p m).2 - (p k).2)
        = ((l • (p m).1 - (p m).2) - h) - ((l • (p k).1 - (p k).2) - h) := by
      rw [smul_sub]; abel
    rw [e] at hd
    have h2 := norm_sub_le ((l • (p m).1 - (p m).2) - h) ((l • (p k).1 - (p k).2) - h)
    rw [le_inv_mul_iff₀ hl]
    linarith [hpn m, hpn k]
  have hC : CauchySeq (fun k => (p k).1) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (l * ε))
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hcau m N) ?_
    have hN' : (0 : ℝ) < N + 1 := by positivity
    have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hN' hm'
    have h3 : 2 / ((N : ℝ) + 1) < l * ε / 2 := by
      have : 4 / (l * ε) < N + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      rw [div_lt_iff₀ hN']
      nlinarith [mul_pos hl hε]
    calc l⁻¹ * (1 / ((m : ℝ) + 1) + 1 / ((N : ℝ) + 1)) ≤ l⁻¹ * (2 / ((N : ℝ) + 1)) := by
          gcongr
          rw [show (2:ℝ) / ((N:ℝ) + 1) = 1 / ((N:ℝ) + 1) + 1 / ((N:ℝ) + 1) by ring]
          linarith
      _ < l⁻¹ * (l * ε / 2) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hC
  have hres : Tendsto (fun k => (l • (p k).1 - (p k).2) - h) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hpn k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun k => (p k).2) atTop (𝓝 (l • f - h)) := by
    have : Tendsto (fun k => l • (p k).1 - ((l • (p k).1 - (p k).2) - h) - h) atTop
        (𝓝 (l • f - 0 - h)) :=
      ((hf.const_smul l).sub hres).sub tendsto_const_nhds
    simp only [sub_zero] at this
    refine this.congr (fun k => ?_)
    abel
  have hmem : (f, l • f - h) ∈ A :=
    hcl.mem_of_tendsto (hf.prodMk_nhds hg) (Eventually.of_forall hpA)
  exact ⟨(f, l • f - h), hmem, by simp⟩

/-- Step 2: a dissipative relation with dense domain is single-valued. -/
lemma single_valued (hA : Diss A) (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {g : E} (h0 : ((0 : E), g) ∈ A) : g = 0 := by
  have key : ∀ fk ∈ A, ∀ ε : ℝ, 0 < ε → ‖fk.1‖ ≤ ‖fk.1 - g‖ + ε := by
    intro fk hfk ε hε
    set t := (‖fk.2‖ + 1) / ε with ht
    have htpos : 0 < t := by positivity
    have hmem : fk + t • ((0 : E), g) ∈ A := A.add_mem hfk (A.smul_mem t h0)
    have hdi := hA _ hmem t htpos
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
      add_zero] at hdi
    have e : t • fk.1 - (fk.2 + t • g) = t • (fk.1 - g) - fk.2 := by
      rw [smul_sub]; abel
    rw [e] at hdi
    have h2 : ‖t • (fk.1 - g) - fk.2‖ ≤ t * ‖fk.1 - g‖ + ‖fk.2‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg htpos.le]
    have h3 : ‖fk.2‖ ≤ t * ε := by
      rw [ht, div_mul_cancel₀ _ hε.ne']; linarith
    have : t * ‖fk.1‖ ≤ t * (‖fk.1 - g‖ + ε) := by nlinarith
    exact le_of_mul_le_mul_left this htpos
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨fk, hfk, hn⟩ := hd g (ε / 3) (by positivity)
  have h1 := key fk hfk (ε / 3) (by positivity)
  have h2 : ‖g‖ ≤ ‖fk.1‖ + ‖fk.1 - g‖ := by
    have := norm_sub_le fk.1 (fk.1 - g)
    simp only [sub_sub_cancel] at this
    linarith [norm_sub_rev fk.1 g]
  linarith

/-- Step 4: the resolvent as a bounded operator. -/
lemma exists_resolvent (hA : Diss A) {l : ℝ} (hl : 0 < l)
    (hs : ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h) :
    ∃ R : E →L[ℝ] E, (∀ h, (R h, l • R h - h) ∈ A) ∧ (∀ h, ‖R h‖ ≤ l⁻¹ * ‖h‖) := by
  have hex : ∀ h : E, ∃ f : E, (f, l • f - h) ∈ A := by
    intro h
    obtain ⟨fg, hfg, he⟩ := hs h
    refine ⟨fg.1, ?_⟩
    have : l • fg.1 - h = fg.2 := by rw [← he]; abel
    rw [this]; exact hfg
  choose r hr using hex
  have uniq : ∀ h : E, ∀ f : E, (f, l • f - h) ∈ A → r h = f := by
    intro h f hf
    have hm := A.sub_mem (hr h) hf
    have := diss_zero hA hl hm (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [smul_sub]; abel)
    exact sub_eq_zero.mp this
  let L : E →ₗ[ℝ] E :=
    { toFun := r
      map_add' := fun x y => by
        refine (uniq (x + y) (r x + r y) ?_).trans rfl
        have := A.add_mem (hr x) (hr y)
        convert this using 1
        simp only [Prod.mk_add_mk, smul_add]; congr 1; abel
      map_smul' := fun s x => by
        refine (uniq (s • x) (s • r x) ?_).trans rfl
        have := A.smul_mem s (hr x)
        convert this using 1
        simp only [Prod.smul_mk, smul_sub, smul_comm l s] }
  have hb : ∀ h, ‖r h‖ ≤ l⁻¹ * ‖h‖ := by
    intro h
    have := hA _ (hr h) l hl
    simp only [sub_sub_cancel] at this
    rw [le_inv_mul_iff₀ hl]; exact this
  exact ⟨L.mkContinuous l⁻¹ hb, fun h => hr h, hb⟩

/-- Step 3a: surjectivity of `l - A` propagates from `l₁` to `(0, 2 l₁)` (Neumann series). -/
lemma range_step [CompleteSpace E] (hA : Diss A) {l₁ : ℝ} (hl₁ : 0 < l₁)
    (hs₁ : ∀ h : E, ∃ fg ∈ A, l₁ • fg.1 - fg.2 = h) {l : ℝ} (hl : 0 < l) (hll : l < 2 * l₁) :
    ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  obtain ⟨R, hR, hRb⟩ := exists_resolvent hA hl₁ hs₁
  have hRn : ‖R‖ ≤ l₁⁻¹ := ContinuousLinearMap.opNorm_le_bound _ (by positivity) hRb
  set K : E →L[ℝ] E := (l₁ - l) • R with hK
  have hKn : ‖K‖ < 1 := by
    calc ‖K‖ ≤ |l₁ - l| * ‖R‖ := by rw [hK, norm_smul, Real.norm_eq_abs]
      _ ≤ |l₁ - l| * l₁⁻¹ := by gcongr
      _ < 1 := by
          rw [← div_eq_mul_inv, div_lt_one hl₁, abs_lt]
          constructor <;> linarith
  intro h
  set U := Units.oneSub K hKn
  set f : E := (↑U⁻¹ : E →L[ℝ] E) (R h) with hf
  have hU : f - K f = R h := by
    have e := congrArg (fun T : E →L[ℝ] E => T (R h)) (Units.mul_inv U)
    simp only [ContinuousLinearMap.mul_apply, Units.val_oneSub, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at e
    rw [← hf] at e
    exact e
  set h' : E := h + (l₁ - l) • f with hh'
  have hRf : R h' = f := by
    rw [hh', map_add, map_smul]
    have : K f = (l₁ - l) • R f := by rw [hK]; rfl
    rw [← this]
    rw [← hU]; abel
  refine ⟨(R h', l₁ • R h' - h'), hR h', ?_⟩
  show l • R h' - (l₁ • R h' - h') = h
  rw [hRf, hh', sub_smul]; abel

/-- Step 3b: full range for every positive `l`. -/
lemma range_all [CompleteSpace E] (hA : Diss A) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hs₀ : ∀ h : E, ∃ fg ∈ A, l₀ • fg.1 - fg.2 = h) {l : ℝ} (hl : 0 < l) :
    ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  have hk : ∀ k : ℕ, ∀ h : E, ∃ fg ∈ A, (l₀ * (3 / 2 : ℝ) ^ k) • fg.1 - fg.2 = h := by
    intro k
    induction k with
    | zero => simpa using hs₀
    | succ k ih =>
      have hp : 0 < l₀ * (3 / 2 : ℝ) ^ k := by positivity
      refine range_step hA hp ih (by positivity) ?_
      rw [pow_succ]; nlinarith
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (l / l₀) (by norm_num : (1 : ℝ) < 3 / 2)
  have hp : 0 < l₀ * (3 / 2 : ℝ) ^ k := by positivity
  refine range_step hA hp (hk k) hl ?_
  rw [div_lt_iff₀ hl₀] at hk'
  nlinarith

/-- Step 4b: a resolvent family on all of `(0, ∞)`. -/
lemma resolvent_family [CompleteSpace E] (hA : Diss A) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hs₀ : ∀ h : E, ∃ fg ∈ A, l₀ • fg.1 - fg.2 = h) :
    ∃ R : ℝ → E →L[ℝ] E, ∀ l : ℝ, 0 < l →
      (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖) := by
  have : ∀ l : ℝ, ∃ R : E →L[ℝ] E, 0 < l →
      (∀ h, (R h, l • R h - h) ∈ A) ∧ (∀ h, ‖R h‖ ≤ l⁻¹ * ‖h‖) := by
    intro l
    by_cases hl : 0 < l
    · obtain ⟨R, h1, h2⟩ := exists_resolvent hA hl (range_all hA hl₀ hs₀ hl)
      exact ⟨R, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose R hR using this
  exact ⟨R, hR⟩

/-- The resolvent inverts `l - A` on the relation. -/
lemma res_eq (hA : Diss A) {l : ℝ} (hl : 0 < l) {R : E →L[ℝ] E}
    (hR : ∀ h, (R h, l • R h - h) ∈ A) {f g : E} (hfg : (f, g) ∈ A) :
    R (l • f - g) = f := by
  have hm := A.sub_mem (hR (l • f - g)) hfg
  have := diss_zero hA hl hm (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [smul_sub]; abel)
  exact sub_eq_zero.mp this

/-- Step 6a: `l R_l h → h` as `l → ∞`, using the dense domain. -/
lemma yosida_tendsto (hA : Diss A) (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    (h : E) : Tendsto (fun l : ℝ => l • R l h) atTop (𝓝 h) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨fg, hfg, hn⟩ := hd h (ε / 3) (by positivity)
  refine ⟨max 1 (3 * (‖fg.2‖ + 1) / ε), fun l hl => ?_⟩
  have hl1 : 0 < l := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hl)
  have hl2 : 3 * (‖fg.2‖ + 1) / ε ≤ l := (le_max_right _ _).trans hl
  obtain ⟨hR1, hR2⟩ := hR l hl1
  have hcon : ∀ x, ‖l • R l x‖ ≤ ‖x‖ := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hl1.le]
    calc l * ‖R l x‖ ≤ l * (l⁻¹ * ‖x‖) := by gcongr; exact hR2 x
      _ = ‖x‖ := by field_simp
  have e1 : l • R l fg.1 - fg.1 = R l fg.2 := by
    have := res_eq hA hl1 hR1 hfg
    rw [map_sub, map_smul] at this
    calc l • R l fg.1 - fg.1 = l • R l fg.1 - (l • R l fg.1 - R l fg.2) := by rw [this]
      _ = R l fg.2 := by abel
  have e2 : ‖R l fg.2‖ < ε / 3 := by
    refine lt_of_le_of_lt (hR2 fg.2) ?_
    rw [inv_mul_lt_iff₀ hl1]
    rw [div_le_iff₀ hε] at hl2
    nlinarith
  rw [dist_eq_norm]
  have split : l • R l h - h = l • R l (h - fg.1) + (l • R l fg.1 - fg.1) + (fg.1 - h) := by
    rw [map_sub, smul_sub]; abel
  rw [split, e1]
  have h3 : ‖l • R l (h - fg.1)‖ < ε / 3 := by
    refine lt_of_le_of_lt (hcon _) ?_
    rw [norm_sub_rev]; exact hn
  calc ‖l • R l (h - fg.1) + R l fg.2 + (fg.1 - h)‖
      ≤ ‖l • R l (h - fg.1)‖ + ‖R l fg.2‖ + ‖fg.1 - h‖ := norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end relation

end P54176b4eR

/-! ## C1: the martingale increment has zero integral over every past event -/

namespace P54176b4e
open EthierKurtz

noncomputable def indUBF {E : Type*} (B : Set E) : UniformBoundedFunction E :=
  ⟨B.indicator 1, memℓp_infty ⟨1, by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ B <;> simp [hx]⟩⟩

lemma indUBF_coe {E : Type*} (B : Set E) : ⇑(indUBF B) = B.indicator 1 := rfl

lemma ubf_bound {E : Type*} (f : UniformBoundedFunction E) (x : E) : |(f : E → ℝ) x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

variable {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]

lemma X_meas {X : ℝ≥0 → Ω → E} (hX : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2)) (t : ℝ≥0) :
    Measurable (X t) :=
  hX.comp (measurable_const.prodMk measurable_id)

lemma intInt_meas {X : ℝ≥0 → Ω → E} (hX : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    {g : E → ℝ} (hg : Measurable g) (a b : ℝ) :
    Measurable (fun ω => ∫ r in a..b, g (X r.toNNReal ω)) := by
  have hF : StronglyMeasurable (fun p : Ω × ℝ => g (X p.2.toNNReal p.1)) :=
    (hg.comp (hX.comp (measurable_snd.real_toNNReal.prodMk measurable_fst))).stronglyMeasurable
  show Measurable fun ω =>
    (∫ r in Ioc a b, g (X r.toNNReal ω)) - ∫ r in Ioc b a, g (X r.toNNReal ω)
  exact (hF.integral_prod_right' (ν := volume.restrict (Ioc a b))).measurable.sub
    (hF.integral_prod_right' (ν := volume.restrict (Ioc b a))).measurable

/-- The martingale increment `f(X v) - f(X u) - ∫_u^v g(X r) dr`. -/
noncomputable def incr (X : ℝ≥0 → Ω → E) (f g : E → ℝ) (u v : ℝ≥0) (ω : Ω) : ℝ :=
  f (X v ω) - f (X u ω) - ∫ r in (u:ℝ)..(v:ℝ), g (X r.toNNReal ω)

lemma incr_meas {X : ℝ≥0 → Ω → E} (hX : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) (u v : ℝ≥0) :
    Measurable (incr X f g u v) :=
  ((hf.comp (X_meas hX v)).sub (hf.comp (X_meas hX u))).sub (intInt_meas hX hg _ _)

lemma incr_bound (X : ℝ≥0 → Ω → E) (fg : UniformBoundedFunction E × UniformBoundedFunction E)
    (u v : ℝ≥0) (ω : Ω) :
    |incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω| ≤ 2 * ‖fg.1‖ + ‖fg.2‖ * |(v:ℝ) - u| := by
  unfold incr
  have h1 := ubf_bound fg.1 (X v ω)
  have h2 := ubf_bound fg.1 (X u ω)
  have h3 : ‖∫ r in (u:ℝ)..(v:ℝ), (fg.2 : E → ℝ) (X r.toNNReal ω)‖ ≤ ‖fg.2‖ * |(v:ℝ) - u| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => by
      rw [Real.norm_eq_abs]; exact ubf_bound fg.2 _)
  rw [Real.norm_eq_abs] at h3
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

lemma incr_integrable {X : ℝ≥0 → Ω → E} (hX : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    {P : Measure Ω} [IsFiniteMeasure P] (fg : UniformBoundedFunction E × UniformBoundedFunction E)
    (hm : Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ)) (u v : ℝ≥0) :
    Integrable (incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v) P :=
  Integrable.of_bound (incr_meas hX hm.1 hm.2 u v).aestronglyMeasurable _
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact incr_bound X fg u v ω)

lemma processPast_le {X : ℝ≥0 → Ω → E} (hX : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (u : ℝ≥0) : processPast X u ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun i => (X_meas hX i.val).comap_le

/-- C1: `∫_G (f(X v) - f(X u) - ∫_u^v g(X r) dr) dP = 0` for every `G ∈ processPast X u`. -/
lemma setIntegral_incr_eq_zero
    {A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E)}
    {μ : Measure E} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → E}
    (hX : SolvesMartingaleProblem A μ P X)
    {fg : UniformBoundedFunction E × UniformBoundedFunction E}
    (hfg : fg ∈ A) (hm : Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    {u v : ℝ≥0} (huv : u ≤ v) :
    ∀ G, MeasurableSet[processPast X u] G →
      ∫ ω in G, incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω ∂P = 0 := by
  have hle := processPast_le hX.1 u
  have hint := incr_integrable hX.1 (P := P) fg hm u v
  have hmart := hX.2.2 fg hfg u v huv
  have htot : ∫ ω, incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω ∂P = 0 := by
    have := hmart 0 Fin.elim0 (fun i => i.elim0) Fin.elim0 (fun i => i.elim0)
    simpa [incr] using this
  refine MeasurableSpace.induction_on_inter (m := processPast X u)
    (C := fun G _ => ∫ ω in G, incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω ∂P = 0)
    (s := piiUnionInter (fun x : Iic u =>
      {S | MeasurableSet[MeasurableSpace.comap (X x.val) ‹MeasurableSpace E›] S}) univ)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact ((generateFrom_piiUnionInter_measurableSet
      (fun x : Iic u => MeasurableSpace.comap (X x.val) ‹MeasurableSpace E›) univ).trans
      iSup_univ).symm
  · exact isPiSystem_piiUnionInter _
      (fun x : Iic u => @MeasurableSpace.isPiSystem_measurableSet Ω
        (MeasurableSpace.comap (X x.val) ‹MeasurableSpace E›)) univ
  · simp
  · rintro t ⟨T, -, F, hF, rfl⟩
    choose! B hB hBF using fun x (hx : x ∈ T) => MeasurableSpace.measurableSet_comap.1 (hF x hx)
    let e := T.equivFin
    have hprod : ∀ ω, ∏ i, (indUBF (B (e.symm i).1) : E → ℝ) (X (e.symm i).1.1 ω)
        = (⋂ x ∈ T, F x).indicator 1 ω := by
      intro ω
      simp only [indUBF_coe]
      rw [e.symm.prod_comp (fun x : T => (B x.1).indicator (1 : E → ℝ) (X x.1.1 ω))]
      rw [Finset.prod_coe_sort T (fun x => (B x).indicator (1 : E → ℝ) (X x.1 ω))]
      by_cases hω : ω ∈ ⋂ x ∈ T, F x
      · rw [indicator_of_mem hω]
        refine Finset.prod_eq_one fun x hx => ?_
        have : ω ∈ F x := mem_iInter₂.1 hω x hx
        rw [← hBF x hx] at this
        simp [indicator_of_mem (show X x.1 ω ∈ B x from this)]
      · rw [indicator_of_notMem hω]
        simp only [mem_iInter₂, not_forall] at hω
        obtain ⟨x, hx, hωx⟩ := hω
        refine Finset.prod_eq_zero hx ?_
        rw [← hBF x hx] at hωx
        simp [indicator_of_notMem (show X x.1 ω ∉ B x from hωx)]
    have hTm : MeasurableSet (⋂ x ∈ T, F x) :=
      Finset.measurableSet_biInter T fun x hx => by
        rw [← hBF x hx]; exact X_meas hX.1 _ (hB x hx)
    have key : ∫ ω, incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω *
        (⋂ x ∈ T, F x).indicator 1 ω ∂P = 0 := by
      refine Eq.trans ?_ (hmart T.card (fun i => (e.symm i).1.1) (fun i => (e.symm i).1.2)
        (fun i => indUBF (B (e.symm i).1)) (fun i => by
          rw [indUBF_coe]; exact measurable_one.indicator (hB _ (e.symm i).2)))
      congr 1; ext ω
      rw [← hprod ω]; rfl
    show ∫ ω in ⋂ x ∈ T, F x, incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω ∂P = 0
    rw [← integral_indicator hTm]
    refine Eq.trans ?_ key
    congr 1; ext ω
    by_cases hω : ω ∈ ⋂ x ∈ T, F x
    · rw [indicator_of_mem hω, indicator_of_mem hω]; simp
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]; simp
  · intro t htm ht
    rw [setIntegral_compl (hle _ htm) hint, ht, htot, sub_zero]
  · intro f hd hfm hf
    rw [integral_iUnion (fun i => hle _ (hfm i)) hd hint.integrableOn]
    simp [hf]

/-- C1': a bounded `processPast X u`-measurable weight annihilates the increment. -/
lemma integral_weight_mul_incr_eq_zero
    {A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E)}
    {μ : Measure E} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → E}
    (hX : SolvesMartingaleProblem A μ P X)
    {fg : UniformBoundedFunction E × UniformBoundedFunction E}
    (hfg : fg ∈ A) (hm : Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    {u v : ℝ≥0} (huv : u ≤ v) {W : Ω → ℝ} (hWm : StronglyMeasurable[processPast X u] W)
    {C : ℝ} (hWb : ∀ ω, |W ω| ≤ C) :
    ∫ ω, W ω * incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω ∂P = 0 := by
  have hle := processPast_le hX.1 u
  have hint := incr_integrable hX.1 (P := P) fg hm u v
  have hce : P[incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v | processPast X u] =ᵐ[P] 0 :=
    (ae_eq_condExp_of_forall_setIntegral_eq hle hint (g := 0)
      (fun s _ _ => integrableOn_zero)
      (fun s hs _ => by
        rw [setIntegral_incr_eq_zero hX hfg hm huv s hs]; simp)
      stronglyMeasurable_zero.aestronglyMeasurable).symm
  have hWint : Integrable (W * incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v) P := by
    refine Integrable.of_bound ((hWm.mono hle).measurable.mul
      (incr_meas hX.1 hm.1 hm.2 u v)).aestronglyMeasurable
      (C * (2 * ‖fg.1‖ + ‖fg.2‖ * |(v:ℝ) - u|)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    exact mul_le_mul (hWb ω) (incr_bound X fg u v ω) (abs_nonneg _)
      ((abs_nonneg _).trans (hWb ω))
  show ∫ ω, (W * incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v) ω ∂P = 0
  rw [← integral_condExp hle]
  rw [integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hWm hWint hint)]
  have h0 : (W * P[incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v | processPast X u]) =ᵐ[P]
      (0 : Ω → ℝ) := hce.mono fun ω h => by simp only [Pi.mul_apply, h, Pi.zero_apply, mul_zero]
  rw [integral_congr_ae h0]
  simp

end P54176b4e

/-! ## C5 glue and C6: forward-equation uniqueness (abstract normed space) -/

namespace P54176b4e

section C6
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma eq_zero_of_abs_le_mul {q c : ℝ} (hc : 0 ≤ c) (h : ∀ η : ℝ, 0 < η → |q| ≤ c * η) :
    q = 0 := by
  by_contra hq
  have hq' : 0 < |q| := abs_pos.mpr hq
  have h1 := h (|q| / (2 * (c + 1))) (by positivity)
  have h2 : c * (|q| / (2 * (c + 1))) < |q| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg hc hq'.le]
  linarith

/-- C5 glue: the closure of a dissipative `A'` with `closure (a - A') = L = closure (dom A')`
solves `l f - g = h` inside `L` for every `l > 0`. -/
lemma glue_range [CompleteSpace V] (A' : Submodule ℝ (V × V))
    (hd : ∀ fg ∈ A', ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ V) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hr1 : closure ((fun fg : V × V => a₀ • fg.1 - fg.2) '' (A' : Set (V × V))) = (L : Set V))
    (hr2 : closure ((fun fg : V × V => fg.1) '' (A' : Set (V × V))) = (L : Set V)) :
    ∀ l : ℝ, 0 < l → ∀ h ∈ L, ∃ fg ∈ closure (A' : Set (V × V)),
      fg.1 ∈ L ∧ fg.2 ∈ L ∧ l • fg.1 - fg.2 = h := by
  have hLcl : IsClosed (L : Set V) := hr2 ▸ isClosed_closure
  haveI : CompleteSpace L := hLcl.completeSpace_coe
  let B : Submodule ℝ (L × L) :=
    (A'.topologicalClosure).comap (L.subtype.prodMap L.subtype)
  have hmemB : ∀ p : L × L, p ∈ B ↔ ((p.1 : V), (p.2 : V)) ∈ closure (A' : Set (V × V)) := by
    intro p
    rw [← A'.topologicalClosure_coe]
    rfl
  have hDiss : P54176b4eR.Diss B := by
    intro p hp lam hlam
    have hS : IsClosed {q : V × V | lam * ‖q.1‖ ≤ ‖lam • q.1 - q.2‖} :=
      isClosed_le (continuous_const.mul continuous_fst.norm)
        ((continuous_const.smul continuous_fst).sub continuous_snd).norm
    have hsub : closure (A' : Set (V × V)) ⊆ {q : V × V | lam * ‖q.1‖ ≤ ‖lam • q.1 - q.2‖} :=
      closure_minimal (fun q hq => hd q hq lam hlam) hS
    exact hsub ((hmemB p).1 hp)
  have hcl : IsClosed (B : Set (L × L)) :=
    A'.isClosed_topologicalClosure.preimage
      (continuous_subtype_val.prodMap continuous_subtype_val)
  have hr : ∀ h : L, ∀ δ : ℝ, 0 < δ → ∃ p ∈ B, ‖(a₀ • p.1 - p.2) - h‖ < δ := by
    intro h δ hδ
    have hh : (h : V) ∈ closure ((fun fg : V × V => a₀ • fg.1 - fg.2) '' (A' : Set (V × V))) := by
      rw [hr1]; exact h.2
    obtain ⟨y, ⟨fg, hfg, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hh δ hδ
    have hf : fg.1 ∈ L := by
      have : fg.1 ∈ closure ((fun fg : V × V => fg.1) '' (A' : Set (V × V))) :=
        subset_closure ⟨fg, hfg, rfl⟩
      rw [hr2] at this; exact this
    have hy' : a₀ • fg.1 - fg.2 ∈ L := by
      have : a₀ • fg.1 - fg.2 ∈
          closure ((fun fg : V × V => a₀ • fg.1 - fg.2) '' (A' : Set (V × V))) :=
        subset_closure ⟨fg, hfg, rfl⟩
      rw [hr1] at this; exact this
    have hg : fg.2 ∈ L := by
      have := L.sub_mem (L.smul_mem a₀ hf) hy'
      simpa using this
    refine ⟨(⟨fg.1, hf⟩, ⟨fg.2, hg⟩), (hmemB _).2 (subset_closure hfg), ?_⟩
    rw [dist_comm, dist_eq_norm] at hy
    exact hy
  have hs₀ : ∀ h : L, ∃ p ∈ B, a₀ • p.1 - p.2 = h :=
    P54176b4eR.range_full hcl hDiss ha₀ hr
  intro l hl h hh
  obtain ⟨p, hp, hpe⟩ := P54176b4eR.range_all hDiss ha₀ hs₀ hl ⟨h, hh⟩
  refine ⟨((p.1 : V), (p.2 : V)), (hmemB p).1 hp, p.1.2, p.2.2, ?_⟩
  have := congrArg Subtype.val hpe
  simpa using this

/-- C6: uniqueness for the forward equation `Φ_b f - Φ_a f = ∫_a^b Φ_r g`. -/
lemma fwd_unique (Φ : ℝ → V → ℝ) {K : ℝ} (hK : 0 ≤ K) (L : Submodule ℝ V)
    (D0 D : Set (V × V))
    (hbound : ∀ r h, |Φ r h| ≤ K * ‖h‖)
    (hsub : ∀ r, ∀ h₁ ∈ L, ∀ h₂ ∈ L, Φ r (h₁ - h₂) = Φ r h₁ - Φ r h₂)
    (hsmul : ∀ r, ∀ h ∈ L, ∀ c : ℝ, Φ r (c • h) = c * Φ r h)
    (hD0L : ∀ fg ∈ D0, fg.1 ∈ L ∧ fg.2 ∈ L)
    (hDL : ∀ fg ∈ D, fg.1 ∈ L ∧ fg.2 ∈ L)
    (hDcl : D ⊆ closure D0)
    (hfwd : ∀ fg ∈ D0, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      Φ b fg.1 - Φ a fg.1 = ∫ r in a..b, Φ r fg.2)
    (h0 : ∀ h ∈ L, Φ 0 h = 0)
    (hdense : ∀ h ∈ L, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ D0, ‖fg.1 - h‖ < δ)
    (hrng : ∀ n : ℕ, ∀ h ∈ L, ∃ fg ∈ D, ((n:ℝ) + 1) • fg.1 - fg.2 = h) :
    ∀ h ∈ L, ∀ r, 0 ≤ r → Φ r h = 0 := by
  have hlip : ∀ r, ∀ h₁ ∈ L, ∀ h₂ ∈ L, |Φ r h₁ - Φ r h₂| ≤ K * ‖h₁ - h₂‖ := by
    intro r h₁ hh₁ h₂ hh₂
    rw [← hsub r h₁ hh₁ h₂ hh₂]; exact hbound r _
  have hinc : ∀ fg ∈ D0, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      |Φ b fg.1 - Φ a fg.1| ≤ K * ‖fg.2‖ * |b - a| := by
    have key : ∀ fg ∈ D0, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
        |Φ b fg.1 - Φ a fg.1| ≤ K * ‖fg.2‖ * |b - a| := by
      intro fg hfg a b ha hab
      rw [hfwd fg hfg a b ha hab, ← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_of_norm_le_const
        (fun r _ => by rw [Real.norm_eq_abs]; exact hbound r _)
    intro fg hfg a b ha hb
    rcases le_total a b with hab | hba
    · exact key fg hfg a b ha hab
    · rw [abs_sub_comm, abs_sub_comm b a]; exact key fg hfg b a hb hba
  have hcont : ∀ h ∈ L, ContinuousOn (fun r => Φ r h) (Ici 0) := by
    intro h hh
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨fg, hfg, hfgh⟩ := hdense h hh (ε / (4 * (K + 1))) (by positivity)
    have hfL := (hD0L fg hfg).1
    have hc : 0 ≤ K * ‖fg.2‖ := mul_nonneg hK (norm_nonneg _)
    refine ⟨ε / (2 * (K * ‖fg.2‖ + 1)), by positivity, fun a ha hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have e1 := hlip a h hh fg.1 hfL
    have e2 := hlip b fg.1 hfL h hh
    have e3 := hinc fg hfg b a hb ha
    rw [norm_sub_rev] at e1
    have hKe : K * ‖fg.1 - h‖ ≤ ε / 4 := by
      calc K * ‖fg.1 - h‖ ≤ (K + 1) * (ε / (4 * (K + 1))) :=
            mul_le_mul (by linarith) hfgh.le (norm_nonneg _) (by linarith)
        _ = ε / 4 := by field_simp <;> ring
    have hd : K * ‖fg.2‖ * |a - b| < ε / 2 := by
      calc K * ‖fg.2‖ * |a - b| ≤ (K * ‖fg.2‖ + 1) * |a - b| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (K * ‖fg.2‖ + 1) * (ε / (2 * (K * ‖fg.2‖ + 1))) :=
            mul_lt_mul_of_pos_left hab (by positivity)
        _ = ε / 2 := by field_simp <;> ring
    calc |Φ a h - Φ b h|
        = |(Φ a h - Φ a fg.1) + (Φ a fg.1 - Φ b fg.1) + (Φ b fg.1 - Φ b h)| := by
          congr 1; ring
      _ ≤ |Φ a h - Φ a fg.1| + |Φ a fg.1 - Φ b fg.1| + |Φ b fg.1 - Φ b h| :=
          abs_add_three _ _ _
      _ < ε := by linarith
  have hfwdD : ∀ fg ∈ D, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      Φ b fg.1 - Φ a fg.1 = ∫ r in a..b, Φ r fg.2 := by
    intro fg hfg a b ha hab
    obtain ⟨hfL, hgL⟩ := hDL fg hfg
    have hsubI : uIcc a b ⊆ Ici 0 := by
      rw [uIcc_of_le hab]; exact fun x hx => ha.trans hx.1
    have hII : ∀ h ∈ L, IntervalIntegrable (fun r => Φ r h) volume a b :=
      fun h hh => ((hcont h hh).mono hsubI).intervalIntegrable
    rw [← sub_eq_zero]
    refine eq_zero_of_abs_le_mul (c := 2 * K + K * (b - a))
      (by nlinarith [mul_nonneg hK (sub_nonneg.2 hab)]) fun η hη => ?_
    obtain ⟨fg', hfg', hd⟩ := Metric.mem_closure_iff.1 (hDcl hfg) η hη
    obtain ⟨hfL', hgL'⟩ := hD0L fg' hfg'
    rw [Prod.dist_eq] at hd
    have hd1 : ‖fg.1 - fg'.1‖ < η := by
      rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_left _ _) hd
    have hd2 : ‖fg.2 - fg'.2‖ < η := by
      rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_right _ _) hd
    have hQ' := hfwd fg' hfg' a b ha hab
    have hint : |(∫ r in a..b, Φ r fg.2) - ∫ r in a..b, Φ r fg'.2| ≤ K * η * (b - a) := by
      rw [← intervalIntegral.integral_sub (hII _ hgL) (hII _ hgL'), ← Real.norm_eq_abs]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := fun r => Φ r fg.2 - Φ r fg'.2) (C := K * η) (fun r _ => by
          rw [Real.norm_eq_abs]
          exact (hlip r _ hgL _ hgL').trans (mul_le_mul_of_nonneg_left hd2.le hK))
      rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
    have e1 := hlip b _ hfL _ hfL'
    have e2 := hlip a _ hfL _ hfL'
    have k1 : K * ‖fg.1 - fg'.1‖ ≤ K * η := mul_le_mul_of_nonneg_left hd1.le hK
    rw [abs_le] at e1 e2 hint ⊢
    constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, hint.1, hint.2, k1]
  have hlap : ∀ fg ∈ D, ∀ l : ℝ, 0 < l →
      ∫ r in Ioi (0:ℝ), Real.exp (-l * r) * Φ r (l • fg.1 - fg.2) = 0 := by
    intro fg hfg l hl
    obtain ⟨hfL, hgL⟩ := hDL fg hfg
    have hlin : ∀ r, Φ r (l • fg.1 - fg.2) = l * Φ r fg.1 - Φ r fg.2 := fun r => by
      rw [hsub r _ (L.smul_mem l hfL) _ hgL, hsmul r _ hfL]
    have hderivΦ : ∀ x, 0 < x → HasDerivAt (fun r => Φ r fg.1) (Φ x fg.2) x := by
      intro x hx
      have hI : HasDerivAt (fun r => ∫ u in (0:ℝ)..r, Φ u fg.2) (Φ x fg.2) x := by
        apply intervalIntegral.integral_hasDerivAt_right
        · exact ((hcont _ hgL).mono (by
            rw [uIcc_of_le hx.le]; exact Icc_subset_Ici_self)).intervalIntegrable
        · exact ((hcont _ hgL).mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter
            isOpen_Ioi x hx
        · exact (hcont _ hgL).continuousAt (Ici_mem_nhds hx)
      refine (hI.const_add (Φ 0 fg.1)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with r hr
      show Φ r fg.1 = Φ 0 fg.1 + ∫ u in (0:ℝ)..r, Φ u fg.2
      have := hfwdD fg hfg 0 r le_rfl (le_of_lt hr)
      linarith
    have hGd : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun r => -(Real.exp (-l * r) * Φ r fg.1))
        (Real.exp (-l * x) * Φ x (l • fg.1 - fg.2)) x := by
      intro x hx
      have he : HasDerivAt (fun r => Real.exp (-l * r)) (Real.exp (-l * x) * (-l * 1)) x :=
        ((hasDerivAt_id' x).const_mul (-l)).exp
      refine ((he.mul (hderivΦ x hx)).neg).congr_deriv ?_
      rw [hlin]; ring
    have hcG : ContinuousOn (fun r => -(Real.exp (-l * r) * Φ r fg.1)) (Ici 0) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
        (hcont _ hfL)).neg
    have hint : IntegrableOn (fun r => Real.exp (-l * r) * Φ r (l • fg.1 - fg.2)) (Ioi 0) :=
      integrableOn_exp_mul (k := fun r => Φ r (l • fg.1 - fg.2)) hl
        (((hcont _ (L.sub_mem (L.smul_mem l hfL) hgL)).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (fun r _ => hbound r _)
    have hlim : Tendsto (fun r => -(Real.exp (-l * r) * Φ r fg.1)) atTop (𝓝 0) := by
      have hexp : Tendsto (fun r : ℝ => Real.exp (-l * r)) atTop (𝓝 0) := by
        have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
        refine h.congr fun r => ?_
        simp [Function.comp, neg_mul]
      have ht : Tendsto (fun r : ℝ => Real.exp (-l * r) * (K * ‖fg.1‖)) atTop (𝓝 0) := by
        simpa using hexp.mul_const (K * ‖fg.1‖)
      refine squeeze_zero_norm (fun r => ?_) ht
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound r _) (Real.exp_pos _).le
    have := integral_Ioi_of_hasDerivAt_of_tendsto (hcG.continuousWithinAt self_mem_Ici)
      hGd hint hlim
    rw [this]
    simp [h0 _ hfL]
  intro h hh
  refine laplace_unique (hcont h hh) (C := K * ‖h‖) (fun r _ => hbound r h) fun n => ?_
  obtain ⟨fg, hfg, rfl⟩ := hrng n h hh
  exact hlap fg hfg _ (by positivity)

end C6

end P54176b4e

/-! ## C3 (forward equation), C7 (separation) helpers -/

namespace P54176b4e
open EthierKurtz

section M
variable {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]

lemma int_mul_bdd {P : Measure Ω} {Y Z : Ω → ℝ} (hY : Integrable Y P)
    (hZ : AEStronglyMeasurable Z P) {C : ℝ} (hb : ∀ᵐ ω ∂P, |Z ω| ≤ C) :
    Integrable (fun ω => Y ω * Z ω) P := by
  refine Integrable.mono' (hY.norm.mul_const C) (hY.1.mul hZ) ?_
  filter_upwards [hb] with ω hω
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)

lemma meas_of_mem_closure {S : Set (UniformBoundedFunction E)}
    (hS : ∀ h ∈ S, Measurable (h : E → ℝ)) :
    ∀ h ∈ closure S, Measurable (h : E → ℝ) := by
  intro h hh
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.1 hh
  exact measurable_of_tendsto_metrizable (fun n => hS _ (hxS n))
    ((lp.uniformContinuous_coe.continuous.tendsto h).comp hx)

lemma integral_condExp_mul' {α : Type*} {m m0 : MeasurableSpace α} {P : @Measure α m0}
    [IsFiniteMeasure P] (hm : m ≤ m0) {U G : α → ℝ} (hU : Integrable U P)
    (hG : StronglyMeasurable[m] G) {C : ℝ} (hb : ∀ᵐ ω ∂P, |G ω| ≤ C) :
    ∫ ω, P[U|m] ω * G ω ∂P = ∫ ω, U ω * G ω ∂P := by
  have hUG : Integrable (U * G) P := int_mul_bdd hU (hG.mono hm).aestronglyMeasurable hb
  show ∫ ω, (P[U|m] * G) ω ∂P = ∫ ω, (U * G) ω ∂P
  rw [← integral_congr_ae (condExp_mul_of_stronglyMeasurable_right hG hUG hU)]
  exact integral_condExp hm

lemma setInt_eq_indicator {P : Measure Ω} {F : Set Ω} (hF : MeasurableSet F) (G : Ω → ℝ) :
    ∫ ω in F, G ω ∂P = ∫ ω, F.indicator (1 : Ω → ℝ) ω * G ω ∂P := by
  rw [← integral_indicator hF]
  congr 1; ext ω
  by_cases hω : ω ∈ F <;> simp [hω]

lemma phi_bound {P : Measure Ω} {W : Ω → ℝ} (hWi : Integrable W P) (T : Ω → E)
    (h : UniformBoundedFunction E) :
    |∫ ω, W ω * (h : E → ℝ) (T ω) ∂P| ≤ (∫ ω, |W ω| ∂P) * ‖h‖ := by
  rw [← integral_mul_const]
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Eventually.of_forall fun ω => abs_nonneg _) (hWi.abs.mul_const _)
    (Eventually.of_forall fun ω => ?_))
  simp only [abs_mul]
  exact mul_le_mul_of_nonneg_left (ubf_bound h _) (abs_nonneg _)

lemma phi_sub {P : Measure Ω} {W : Ω → ℝ} (hWi : Integrable W P) {T : Ω → E}
    (hT : Measurable T) (h₁ h₂ : UniformBoundedFunction E)
    (hm₁ : Measurable (h₁ : E → ℝ)) (hm₂ : Measurable (h₂ : E → ℝ)) :
    ∫ ω, W ω * ((h₁ - h₂ : UniformBoundedFunction E) : E → ℝ) (T ω) ∂P =
      (∫ ω, W ω * (h₁ : E → ℝ) (T ω) ∂P) - ∫ ω, W ω * (h₂ : E → ℝ) (T ω) ∂P := by
  have hi1 : Integrable (fun ω => W ω * (h₁ : E → ℝ) (T ω)) P :=
    int_mul_bdd hWi (hm₁.comp hT).aestronglyMeasurable
      (Eventually.of_forall fun ω => ubf_bound h₁ _)
  have hi2 : Integrable (fun ω => W ω * (h₂ : E → ℝ) (T ω)) P :=
    int_mul_bdd hWi (hm₂.comp hT).aestronglyMeasurable
      (Eventually.of_forall fun ω => ubf_bound h₂ _)
  rw [← integral_sub hi1 hi2]
  congr 1; ext ω
  exact mul_sub (W ω) ((h₁ : E → ℝ) (T ω)) ((h₂ : E → ℝ) (T ω))

lemma phi_smul {P : Measure Ω} (W : Ω → ℝ) (T : Ω → E) (h : UniformBoundedFunction E) (c : ℝ) :
    ∫ ω, W ω * ((c • h : UniformBoundedFunction E) : E → ℝ) (T ω) ∂P =
      c * ∫ ω, W ω * (h : E → ℝ) (T ω) ∂P := by
  rw [← integral_const_mul]
  congr 1; ext ω
  show W ω * (c * (h : E → ℝ) (T ω)) = c * (W ω * (h : E → ℝ) (T ω))
  ring

lemma integral_weight_mul_incr_eq_zero'
    {A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E)}
    {μ : Measure E} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → E}
    (hX : SolvesMartingaleProblem A μ P X)
    {fg : UniformBoundedFunction E × UniformBoundedFunction E}
    (hfg : fg ∈ A) (hm : Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    {u v : ℝ≥0} (huv : u ≤ v) {W : Ω → ℝ} (hWm : StronglyMeasurable[processPast X u] W)
    (hWi : Integrable W P) :
    ∫ ω, W ω * incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v ω ∂P = 0 := by
  have hle := processPast_le hX.1 u
  have hint := incr_integrable hX.1 (P := P) fg hm u v
  have hce : P[incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v | processPast X u] =ᵐ[P] 0 :=
    (ae_eq_condExp_of_forall_setIntegral_eq hle hint (g := 0)
      (fun s _ _ => integrableOn_zero)
      (fun s hs _ => by
        rw [setIntegral_incr_eq_zero hX hfg hm huv s hs]; simp)
      stronglyMeasurable_zero.aestronglyMeasurable).symm
  have hWint : Integrable (W * incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v) P :=
    int_mul_bdd hWi (incr_meas hX.1 hm.1 hm.2 u v).aestronglyMeasurable
      (Eventually.of_forall fun ω => incr_bound X fg u v ω)
  show ∫ ω, (W * incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v) ω ∂P = 0
  rw [← integral_condExp hle]
  rw [integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hWm hWint hint)]
  have h0 : (W * P[incr X (fg.1 : E → ℝ) (fg.2 : E → ℝ) u v | processPast X u]) =ᵐ[P]
      (0 : Ω → ℝ) := hce.mono fun ω h => by simp only [Pi.mul_apply, h, Pi.zero_apply, mul_zero]
  rw [integral_congr_ae h0]
  simp

lemma fubini_weight {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → E}
    (hX : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2)) {g : E → ℝ} (hg : Measurable g) {C : ℝ}
    (hgb : ∀ x, |g x| ≤ C) {W : Ω → ℝ} (hWi : Integrable W P) {u v : ℝ} (huv : u ≤ v) :
    ∫ ω, W ω * (∫ r in u..v, g (X r.toNNReal ω)) ∂P =
      ∫ r in u..v, ∫ ω, W ω * g (X r.toNNReal ω) ∂P := by
  simp only [intervalIntegral.integral_of_le huv]
  have hGm : Measurable (fun p : Ω × ℝ => g (X p.2.toNNReal p.1)) :=
    hg.comp (hX.comp (measurable_snd.real_toNNReal.prodMk measurable_fst))
  have hF : Integrable (Function.uncurry fun (ω : Ω) (r : ℝ) => W ω * g (X r.toNNReal ω))
      (P.prod (volume.restrict (Ioc u v))) := by
    refine Integrable.mono' ((hWi.norm.mul_const C).comp_fst (volume.restrict (Ioc u v)))
      ((hWi.comp_fst (volume.restrict (Ioc u v))).1.mul hGm.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨ω, r⟩ := p
    simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hgb _) (abs_nonneg _)
  calc ∫ ω, W ω * (∫ r in Ioc u v, g (X r.toNNReal ω)) ∂P
      = ∫ ω, (∫ r in Ioc u v, W ω * g (X r.toNNReal ω)) ∂P := by
        congr 1; ext ω; rw [integral_const_mul]
    _ = _ := integral_integral_swap hF

/-- C3: the forward equation for a past-measurable integrable weight. -/
lemma fwd_eq {A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E)}
    {μ : Measure E} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → E}
    (hX : SolvesMartingaleProblem A μ P X)
    {fg : UniformBoundedFunction E × UniformBoundedFunction E}
    (hfg : fg ∈ A) (hm : Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    {s : ℝ≥0} {W : Ω → ℝ} (hWm : StronglyMeasurable[processPast X s] W) (hWi : Integrable W P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ ω, W ω * (fg.1 : E → ℝ) (X (s + b.toNNReal) ω) ∂P) -
      ∫ ω, W ω * (fg.1 : E → ℝ) (X (s + a.toNNReal) ω) ∂P =
    ∫ r in a..b, ∫ ω, W ω * (fg.2 : E → ℝ) (X (s + r.toNNReal) ω) ∂P := by
  have hb : 0 ≤ b := ha.trans hab
  have hsu : ∀ c : ℝ, 0 ≤ c → ((s + c.toNNReal : ℝ≥0) : ℝ) = (s : ℝ) + c := fun c hc => by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hc]
  have huv : s + a.toNNReal ≤ s + b.toNNReal := add_le_add le_rfl (Real.toNNReal_le_toNNReal hab)
  have hmono : processPast X s ≤ processPast X (s + a.toNNReal) :=
    iSup_le fun i => le_iSup_of_le
      (⟨i.1, (Set.mem_Iic.1 i.2).trans le_self_add⟩ : Set.Iic (s + a.toNNReal)) le_rfl
  have h0 := integral_weight_mul_incr_eq_zero' hX hfg hm huv (hWm.mono hmono) hWi
  have hb1 : ∀ c : ℝ≥0, Integrable (fun ω => W ω * (fg.1 : E → ℝ) (X c ω)) P := fun c =>
    int_mul_bdd hWi (hm.1.comp (X_meas hX.1 c)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ubf_bound fg.1 _)
  have hbI : Integrable (fun ω => W ω * ∫ r in ((s + a.toNNReal : ℝ≥0) : ℝ)..((s + b.toNNReal : ℝ≥0) : ℝ),
      (fg.2 : E → ℝ) (X r.toNNReal ω)) P :=
    int_mul_bdd hWi (intInt_meas hX.1 hm.2 _ _).aestronglyMeasurable
      (C := ‖fg.2‖ * |((s + b.toNNReal : ℝ≥0) : ℝ) - ((s + a.toNNReal : ℝ≥0) : ℝ)|)
      (Eventually.of_forall fun ω => by
        have := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := ((s + a.toNNReal : ℝ≥0) : ℝ)) (b := ((s + b.toNNReal : ℝ≥0) : ℝ))
          (f := fun r => (fg.2 : E → ℝ) (X r.toNNReal ω)) (C := ‖fg.2‖)
          (fun r _ => by rw [Real.norm_eq_abs]; exact ubf_bound fg.2 _)
        rw [Real.norm_eq_abs] at this
        exact this)
  have hb12 : Integrable (fun ω => W ω * (fg.1 : E → ℝ) (X (s + b.toNNReal) ω) -
      W ω * (fg.1 : E → ℝ) (X (s + a.toNNReal) ω)) P := (hb1 _).sub (hb1 _)
  unfold incr at h0
  simp only [mul_sub] at h0
  rw [integral_sub hb12 hbI, integral_sub (hb1 _) (hb1 _),
    fubini_weight hX.1 hm.2 (ubf_bound fg.2) hWi (NNReal.coe_le_coe.2 huv),
    hsu a ha, hsu b hb] at h0
  have hshift : ∫ r in a..b, ∫ ω, W ω * (fg.2 : E → ℝ) (X (s + r.toNNReal) ω) ∂P =
      ∫ r in (s:ℝ) + a..(s:ℝ) + b, ∫ ω, W ω * (fg.2 : E → ℝ) (X r.toNNReal ω) ∂P := by
    rw [← intervalIntegral.integral_comp_add_left
      (fun r => ∫ ω, W ω * (fg.2 : E → ℝ) (X r.toNNReal ω) ∂P) (s:ℝ)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 ≤ r := by
      rw [uIcc_of_le hab] at hr; exact ha.trans hr.1
    simp only [Real.toNNReal_add (NNReal.coe_nonneg s) hr0, Real.toNNReal_coe]
  rw [hshift]
  linarith

/-- C7: separation lifted to finite measures of equal mass `≤ 1`. -/
lemma sep_lift (L : Submodule ℝ (UniformBoundedFunction E))
    (hLmeas : ∀ h ∈ L, Measurable (h : E → ℝ))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (ν₁ ν₂ : Measure E) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hmass : ν₁ univ = ν₂ univ) (hle : ν₁ univ ≤ 1)
    (hL : ∀ h ∈ L, ∫ x, (h : E → ℝ) x ∂ν₁ = ∫ x, (h : E → ℝ) x ∂ν₂) : ν₁ = ν₂ := by
  have hne : (1 - ν₁ univ) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hm : ∀ ν : Measure E, ν univ = ν₁ univ → (ν + (1 - ν₁ univ).toNNReal • μ) univ = 1 := by
    intro ν hν
    rw [Measure.add_apply, Measure.smul_apply, hν, measure_univ (μ := μ), ENNReal.smul_def,
      smul_eq_mul, mul_one, ENNReal.coe_toNNReal hne, add_tsub_cancel_of_le hle]
  have hint : ∀ (ν : Measure E), IsFiniteMeasure ν → ∀ h ∈ L, Integrable (h : E → ℝ) ν :=
    fun ν _ h hh => Integrable.of_bound (hLmeas h hh).aestronglyMeasurable ‖h‖
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact ubf_bound h x)
  have heq := hsep (ν₁ + (1 - ν₁ univ).toNNReal • μ) (ν₂ + (1 - ν₁ univ).toNNReal • μ)
    ⟨hm ν₁ rfl⟩ ⟨hm ν₂ hmass.symm⟩ (fun h => by
      rw [integral_add_measure (hint ν₁ inferInstance _ h.2) (hint _ inferInstance _ h.2),
        integral_add_measure (hint ν₂ inferInstance _ h.2) (hint _ inferInstance _ h.2),
        hL _ h.2])
  ext s hs
  have := congrArg (fun ν : Measure E => ν s) heq
  simp only [Measure.add_apply] at this
  exact (ENNReal.add_left_inj (measure_ne_top _ _)).1 this

end M

end P54176b4e

open P54176b4e in
set_option maxHeartbeats 1000000 in
open MeasureTheory Filter TopologicalSpace NNReal ENNReal Topology EthierKurtz in
theorem solution
    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MetricSpace E] [BorelSpace E]
    [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ →
      IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) =
        ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X)
    :
    ∀ (s t : ℝ≥0) (f : UniformBoundedFunction E),
      Measurable (f : E → ℝ) →
      P[fun ω => f (X (s + t) ω) | processPast X s] =ᵐ[P]
        P[fun ω => f (X (s + t) ω) |
          MeasurableSpace.comap (X s) ‹MeasurableSpace E›] := by
  intro s t f hf
  have hσle : (MeasurableSpace.comap (X s) ‹MeasurableSpace E›) ≤ processPast X s :=
    le_iSup (fun r : Set.Iic s => MeasurableSpace.comap (X r.val) ‹MeasurableSpace E›) ⟨s, Set.mem_Iic.2 le_rfl⟩
  have hpast := processPast_le hX.1 s
  have hσm : (MeasurableSpace.comap (X s) ‹MeasurableSpace E›) ≤ ‹MeasurableSpace Ω› := hσle.trans hpast
  have hT : Measurable (X (s + t)) := X_meas hX.1 _
  obtain ⟨a₀, ha₀, hr1, hr2⟩ := hrange
  have hLmeas : ∀ h ∈ L, Measurable (h : E → ℝ) := by
    intro h hh
    have : h ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) := by rw [hr2]; exact hh
    refine meas_of_mem_closure (fun h' hh' => ?_) h this
    obtain ⟨fg, hfg, rfl⟩ := hh'
    exact (hAmeas fg (hsub hfg)).1
  have hA'L : ∀ fg ∈ (A' : Set (UniformBoundedFunction E × UniformBoundedFunction E)),
      fg.1 ∈ L ∧ fg.2 ∈ L := by
    intro fg hfg
    have hf1 : fg.1 ∈ L := by
      have : fg.1 ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
          fg.1) '' (A' : Set _)) := subset_closure ⟨fg, hfg, rfl⟩
      rw [hr2] at this; exact this
    have hy : a₀ • fg.1 - fg.2 ∈ L := by
      have : a₀ • fg.1 - fg.2 ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
          a₀ • fg.1 - fg.2) '' (A' : Set _)) := subset_closure ⟨fg, hfg, rfl⟩
      rw [hr1] at this; exact this
    exact ⟨hf1, by simpa using L.sub_mem (L.smul_mem a₀ hf1) hy⟩
  have hdense : ∀ h ∈ L, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ (A' : Set (UniformBoundedFunction E ×
      UniformBoundedFunction E)), ‖fg.1 - h‖ < δ := by
    intro h hh δ hδ
    have : h ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) := by rw [hr2]; exact hh
    obtain ⟨y, ⟨fg, hfg, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 this δ hδ
    exact ⟨fg, hfg, by rw [← dist_eq_norm, dist_comm]; exact hy⟩
  have hrng : ∀ n : ℕ, ∀ h ∈ L, ∃ fg ∈ {fg : UniformBoundedFunction E × UniformBoundedFunction E |
      fg ∈ closure (A' : Set _) ∧ fg.1 ∈ L ∧ fg.2 ∈ L}, ((n:ℝ) + 1) • fg.1 - fg.2 = h := by
    intro n h hh
    obtain ⟨fg, hcl, h1, h2, he⟩ := glue_range A' (fun fg hfg a ha => hdiss fg (hsub hfg) a ha)
      L ha₀ hr1 hr2 ((n:ℝ) + 1) (by positivity) h hh
    exact ⟨fg, ⟨hcl, h1, h2⟩, he⟩
  -- Step A: the weight `1_F - P[1_F | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)]` annihilates `h(X(s+t))` for `h ∈ L`
  have stepA : ∀ F, MeasurableSet[processPast X s] F → ∀ h ∈ L,
      ∫ ω, (F.indicator (1 : Ω → ℝ) ω - P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω) *
        (h : E → ℝ) (X (s + t) ω) ∂P = 0 := by
    intro F hF
    have hFm : MeasurableSet F := hpast _ hF
    have hWi : Integrable (fun ω => F.indicator (1 : Ω → ℝ) ω - P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω) P :=
      ((integrable_const (1:ℝ)).indicator hFm).sub integrable_condExp
    have hWm : StronglyMeasurable[processPast X s]
        (fun ω => F.indicator (1 : Ω → ℝ) ω - P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω) :=
      ((stronglyMeasurable_const (b := (1:ℝ))).indicator hF).sub
        (stronglyMeasurable_condExp.mono hσle)
    have h0' : ∀ h ∈ L, ∫ ω, (F.indicator (1 : Ω → ℝ) ω - P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω) *
        (h : E → ℝ) (X (s + (0:ℝ).toNNReal) ω) ∂P = 0 := by
      intro h hh
      simp only [Real.toNNReal_zero, add_zero]
      have hH : StronglyMeasurable[(MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] (fun ω => (h : E → ℝ) (X s ω)) :=
        ((hLmeas h hh).comp (comap_measurable (X s))).stronglyMeasurable
      have hFi : Integrable (F.indicator (1 : Ω → ℝ)) P := (integrable_const (1:ℝ)).indicator hFm
      have ht := integral_condExp_mul' hσm hFi hH (C := ‖h‖)
        (Eventually.of_forall fun ω => ubf_bound h _)
      simp only [sub_mul]
      rw [integral_sub (int_mul_bdd hFi (hH.mono hσm).aestronglyMeasurable
          (Eventually.of_forall fun ω => ubf_bound h _))
        (int_mul_bdd integrable_condExp (hH.mono hσm).aestronglyMeasurable
          (Eventually.of_forall fun ω => ubf_bound h _)), ht, sub_self]
    have key := fwd_unique
      (fun (r : ℝ) (h : UniformBoundedFunction E) => ∫ ω, (F.indicator (1 : Ω → ℝ) ω - P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω) *
        (h : E → ℝ) (X (s + r.toNNReal) ω) ∂P)
      (integral_nonneg fun ω => abs_nonneg _) L (A' : Set _)
      {fg | fg ∈ closure (A' : Set _) ∧ fg.1 ∈ L ∧ fg.2 ∈ L}
      (fun r h => phi_bound hWi _ h)
      (fun r h₁ hh₁ h₂ hh₂ => phi_sub hWi (X_meas hX.1 _) h₁ h₂ (hLmeas _ hh₁) (hLmeas _ hh₂))
      (fun r h _ c => phi_smul _ _ h c)
      hA'L (fun fg hfg => hfg.2) (fun fg hfg => hfg.1)
      (fun fg hfg a b ha hab => fwd_eq hX (hsub hfg) (hAmeas fg (hsub hfg)) hWm hWi ha hab)
      h0' hdense hrng
    intro h hh
    have := key h hh t t.2
    simpa only [Real.toNNReal_coe] using this
  -- Step B: separation gives `∫ 1_F f(X(s+t)) = ∫ P[1_F|(MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] f(X(s+t))`
  have stepB : ∀ F, MeasurableSet[processPast X s] F →
      ∫ ω, F.indicator (1 : Ω → ℝ) ω * f (X (s + t) ω) ∂P =
        ∫ ω, P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω * f (X (s + t) ω) ∂P := by
    intro F hF
    have hFm : MeasurableSet F := hpast _ hF
    have hFi : Integrable (F.indicator (1 : Ω → ℝ)) P := (integrable_const (1:ℝ)).indicator hFm
    have hYm : Measurable (P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)]) :=
      (stronglyMeasurable_condExp.mono hσm).measurable
    have hY0 : 0 ≤ᵐ[P] P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] :=
      condExp_nonneg (Eventually.of_forall fun ω =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    haveI : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω)) :=
      isFiniteMeasure_withDensity_ofReal integrable_condExp.2
    have hI1 : ∀ k : UniformBoundedFunction E, Measurable (k : E → ℝ) →
        ∫ x, (k : E → ℝ) x ∂((P.restrict F).map (X (s + t))) =
          ∫ ω, F.indicator (1 : Ω → ℝ) ω * k (X (s + t) ω) ∂P := by
      intro k hk
      rw [integral_map hT.aemeasurable hk.aestronglyMeasurable, setInt_eq_indicator hFm]
    have hI2 : ∀ k : UniformBoundedFunction E, Measurable (k : E → ℝ) →
        ∫ x, (k : E → ℝ) x ∂((P.withDensity fun ω =>
          ENNReal.ofReal (P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω)).map (X (s + t))) =
          ∫ ω, P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω * k (X (s + t) ω) ∂P := by
      intro k hk
      rw [integral_map hT.aemeasurable hk.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul hYm.ennreal_ofReal
          (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae ?_
      filter_upwards [hY0] with ω hω
      simp [ENNReal.toReal_ofReal hω]
    have hmass1 : ((P.restrict F).map (X (s + t))) univ = P F := by
      rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
    have hmass2 : ((P.withDensity fun ω =>
        ENNReal.ofReal (P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω)).map (X (s + t))) univ = P F := by
      rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal integrable_condExp hY0, integral_condExp hσm,
        integral_indicator_one hFm]
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    have heq := sep_lift L hLmeas hsep μ _ _ (hmass1.trans hmass2.symm)
      (hmass1 ▸ prob_le_one) (fun h hh => by
        have i1 : Integrable (fun ω => F.indicator (1 : Ω → ℝ) ω * (h : E → ℝ) (X (s + t) ω)) P :=
          int_mul_bdd hFi ((hLmeas h hh).comp hT).aestronglyMeasurable
            (Eventually.of_forall fun ω => ubf_bound h _)
        have i2 : Integrable (fun ω => P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω * (h : E → ℝ) (X (s + t) ω)) P :=
          int_mul_bdd integrable_condExp ((hLmeas h hh).comp hT).aestronglyMeasurable
            (Eventually.of_forall fun ω => ubf_bound h _)
        rw [hI1 h (hLmeas h hh), hI2 h (hLmeas h hh), ← sub_eq_zero,
          ← integral_sub i1 i2, ← stepA F hF h hh]
        congr 1; ext ω; ring)
    rw [← hI1 f hf, ← hI2 f hf, heq]
  -- Step C: identify the conditional expectations
  have hZi : Integrable (fun ω => f (X (s + t) ω)) P :=
    Integrable.of_bound (hf.comp hT).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact ubf_bound f _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hpast hZi
    (g := P[fun ω => f (X (s + t) ω) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)]) (fun F _ _ => integrable_condExp.integrableOn)
    (fun F hF _ => ?_) (stronglyMeasurable_condExp.mono hσle).aestronglyMeasurable).symm
  have hFm : MeasurableSet F := hpast _ hF
  have hFi : Integrable (F.indicator (1 : Ω → ℝ)) P := (integrable_const (1:ℝ)).indicator hFm
  have hZb : ∀ᵐ ω ∂P, |P[fun ω => f (X (s + t) ω) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω| ≤ ((‖f‖₊ : ℝ≥0) : ℝ) :=
    ae_bdd_condExp_of_ae_bdd (Eventually.of_forall fun ω => by
      rw [coe_nnnorm]; exact ubf_bound f _)
  have hYb : ∀ᵐ ω ∂P, |P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω| ≤ ((1 : ℝ≥0) : ℝ) :=
    ae_bdd_condExp_of_ae_bdd (Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ F <;> simp [hω])
  rw [setInt_eq_indicator hFm, setInt_eq_indicator hFm,
    ← integral_condExp_mul' hσm hFi stronglyMeasurable_condExp hZb]
  calc ∫ ω, P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω * P[fun ω => f (X (s + t) ω) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω ∂P
      = ∫ ω, P[fun ω => f (X (s + t) ω) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω * P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω ∂P := by
        congr 1; ext ω; ring
    _ = ∫ ω, f (X (s + t) ω) * P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω ∂P :=
        integral_condExp_mul' hσm hZi stronglyMeasurable_condExp hYb
    _ = ∫ ω, P[F.indicator (1 : Ω → ℝ) | (MeasurableSpace.comap (X s) ‹MeasurableSpace E›)] ω * f (X (s + t) ω) ∂P := by
        congr 1; ext ω; ring
    _ = ∫ ω, F.indicator (1 : Ω → ℝ) ω * f (X (s + t) ω) ∂P := (stepB F hF).symm
