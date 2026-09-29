-- Prove2me | solution 1 for CaiCandesShen.Convergence.uzawa_converges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:48:34.661665+00:00
-- url     : https://prove2.me/submissions/2a070a93-ba21-42c1-8aac-e0203ff31dec

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations
open Filter Topology

namespace CaiCandesShen.Convergence

open scoped InnerProductSpace

section AuxAbstract

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem aux_ucv_abstract (phi : H → ℝ) (hphi : LowerSemicontinuous phi) (A : H →ₗ[ℝ] K) (A' : K → H)
    (hadj : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A' y⟫_ℝ) (L : ℝ) (hL : ∀ x, ‖A x‖ ≤ L * ‖x‖) (b : K) (xb : H)
    (hxb : A xb = b) (δ : ℕ → ℝ) (a C : ℝ) (ha : 0 < a) (hC : C * L ^ 2 < 2)
    (hδ : ∀ k, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C) (X : ℕ → H) (y : ℕ → K) (hy0 : y 0 = 0)
    (hP : ∀ k W, ⟪A' (y k) - X (k + 1), W - X (k + 1)⟫_ℝ ≤ phi W - phi (X (k + 1)))
    (hy : ∀ k, y (k + 1) = y k + δ (k + 1) • (b - A (X (k + 1)))) :
    ∃ xs, A xs = b ∧ Tendsto X atTop (𝓝 xs) ∧
      ∀ W, A W = b → phi xs + ‖xs‖ ^ 2 / 2 + ‖W - xs‖ ^ 2 / 2 ≤ phi W + ‖W‖ ^ 2 / 2 := by
  set f : H → ℝ := fun W => phi W + ‖W‖ ^ 2 / 2 with hf
  set Lg : H → K → ℝ := fun W v => f W + ⟪v, b - A W⟫_ℝ with hLg
  set d : ℕ → K := fun k => b - A (X (k + 1)) with hd
  set G : ℕ → ℝ := fun k => Lg (X (k + 1)) (y k) with hG
  have hAc : Continuous A := LinearMap.continuous_of_finiteDimensional A
  -- step (b)
  have hb : ∀ k W, G k + ‖W - X (k + 1)‖ ^ 2 / 2 ≤ Lg W (y k) := by
    intro k W
    have h := hP k W
    have h1 : ⟪y k, b - A W⟫_ℝ - ⟪y k, b - A (X (k + 1))⟫_ℝ
        = ⟪A' (y k), X (k + 1)⟫_ℝ - ⟪A' (y k), W⟫_ℝ := by
      rw [← inner_sub_right, sub_sub_sub_cancel_left, ← map_sub, real_inner_comm, hadj,
        real_inner_comm, inner_sub_right]
    have h2 := norm_sub_sq_real W (X (k + 1))
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq] at h
    have h3 := real_inner_comm W (X (k + 1))
    simp only [hG, hLg, hf]
    linarith
  have hδ1 : ∀ k, a ≤ δ (k + 1) ∧ δ (k + 1) ≤ C := fun k => hδ (k + 1) (by omega)
  have haC : a ≤ C := (hδ1 0).1.trans (hδ1 0).2
  have hC0 : 0 < C := ha.trans_le haC
  set β : ℝ := a * (1 - C * L ^ 2 / 2) with hβ
  have hβpos : 0 < β := by
    rw [hβ]; apply mul_pos ha; linarith
  -- step (c)
  have hmono : ∀ k, G k + β * ‖d k‖ ^ 2 ≤ G (k + 1) := by
    intro k
    have h := hb k (X (k + 2))
    obtain ⟨hk1, hk2⟩ := hδ1 k
    set Δ := X (k + 2) - X (k + 1) with hΔ
    have hd1 : d (k + 1) = d k - A Δ := by
      simp only [hd, hΔ, map_sub]; abel
    have hG1 : G (k + 1) = f (X (k + 2)) + ⟪y k, d (k + 1)⟫_ℝ + δ (k + 1) * ⟪d k, d (k + 1)⟫_ℝ := by
      simp only [hG, hLg]
      rw [hy k, inner_add_left, real_inner_smul_left]
      simp only [hd]
      ring
    have hL1 : Lg (X (k + 2)) (y k) = f (X (k + 2)) + ⟪y k, d (k + 1)⟫_ℝ := rfl
    have hin : ⟪d k, d (k + 1)⟫_ℝ = ‖d k‖ ^ 2 - ⟪d k, A Δ⟫_ℝ := by
      rw [hd1, inner_sub_right, real_inner_self_eq_norm_sq]
    have hcs : ⟪d k, A Δ⟫_ℝ ≤ ‖d k‖ * (L * ‖Δ‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hL Δ) (norm_nonneg _))
    have hδL : δ (k + 1) * L ^ 2 ≤ C * L ^ 2 := mul_le_mul_of_nonneg_right hk2 (sq_nonneg L)
    have hsq := sq_nonneg (δ (k + 1) * L * ‖d k‖ - ‖Δ‖)
    have hdpos : 0 ≤ ‖d k‖ ^ 2 := sq_nonneg _
    have hkey : β * ‖d k‖ ^ 2 ≤ δ (k + 1) * ‖d k‖ ^ 2 - δ (k + 1) * (‖d k‖ * (L * ‖Δ‖))
        + ‖Δ‖ ^ 2 / 2 := by
      have e1 : δ (k + 1) * (‖d k‖ * (L * ‖Δ‖)) ≤
          (δ (k + 1) * L * ‖d k‖) ^ 2 / 2 + ‖Δ‖ ^ 2 / 2 := by nlinarith
      have e2 : β * ‖d k‖ ^ 2 ≤ δ (k + 1) * ‖d k‖ ^ 2 - (δ (k + 1) * L * ‖d k‖) ^ 2 / 2 := by
        have : (δ (k + 1) * L * ‖d k‖) ^ 2 / 2 = δ (k + 1) * (δ (k + 1) * L ^ 2) * ‖d k‖ ^ 2 / 2 := by
          ring
        rw [this, hβ]
        have h3 : 0 ≤ (δ (k + 1) - a) * (1 - C * L ^ 2 / 2) * ‖d k‖ ^ 2 := by
          apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hdpos
        have h4 : δ (k + 1) * (δ (k + 1) * L ^ 2) * ‖d k‖ ^ 2 / 2 ≤
            δ (k + 1) * (C * L ^ 2) * ‖d k‖ ^ 2 / 2 := by
          have : 0 ≤ δ (k + 1) * ‖d k‖ ^ 2 / 2 := by
            have : 0 ≤ δ (k + 1) := by linarith
            positivity
          nlinarith
        nlinarith
      linarith
    have hδpos : 0 ≤ δ (k + 1) := by linarith
    have := mul_le_mul_of_nonneg_left hcs hδpos
    rw [hG1]
    rw [hL1] at h
    rw [hin]
    nlinarith
  have hGmono : Monotone G := monotone_nat_of_le_succ fun k => by
    have := hmono k; have : 0 ≤ β * ‖d k‖ ^ 2 := by positivity
    linarith
  have hGle : ∀ W, A W = b → ∀ k, G k + ‖W - X (k + 1)‖ ^ 2 / 2 ≤ f W := by
    intro W hW k
    have := hb k W
    simp only [hLg, hW, sub_self, inner_zero_right, add_zero] at this
    exact this
  have hGub : ∀ k, G k ≤ f xb := fun k => by
    have := hGle xb hxb k; have : 0 ≤ ‖xb - X (k + 1)‖ ^ 2 / 2 := by positivity
    linarith
  have hsum : ∀ K, G 0 + β * ∑ k ∈ Finset.range K, ‖d k‖ ^ 2 ≤ G K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hmono K
      linarith
  set M : ℝ := (f xb - G 0) / β with hM
  have hsumM : ∀ K, ∑ k ∈ Finset.range K, ‖d k‖ ^ 2 ≤ M := by
    intro K
    rw [hM, le_div_iff₀ hβpos]
    have := hsum K; have := hGub K
    linarith
  have hM0 : 0 ≤ M := by
    have := hsumM 0; simpa using this
  have hsumm : Summable (fun k => ‖d k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hsumM
  have hdsq0 : Tendsto (fun k => ‖d k‖ ^ 2) atTop (𝓝 0) := hsumm.tendsto_atTop_zero
  have hd0 : Tendsto d atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun k => Real.sqrt (‖d k‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hdsq0
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  -- bound on y
  have hyb : ∀ k, ‖y k‖ ≤ C * ∑ j ∈ Finset.range k, ‖d j‖ := by
    intro k
    induction k with
    | zero => simp [hy0]
    | succ k ih =>
      rw [hy k, Finset.sum_range_succ, mul_add]
      obtain ⟨hk1, hk2⟩ := hδ1 k
      calc ‖y k + δ (k + 1) • (b - A (X (k + 1)))‖
          ≤ ‖y k‖ + ‖δ (k + 1) • (b - A (X (k + 1)))‖ := norm_add_le _ _
        _ = ‖y k‖ + δ (k + 1) * ‖d k‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        _ ≤ C * ∑ j ∈ Finset.range k, ‖d j‖ + C * ‖d k‖ := by
          gcongr
  have hyb2 : ∀ k, ‖y k‖ ^ 2 ≤ C ^ 2 * k * M := by
    intro k
    have h1 := hyb k
    have h2 : (∑ j ∈ Finset.range k, ‖d j‖) ^ 2 ≤ k * ∑ j ∈ Finset.range k, ‖d j‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := fun j => ‖d j‖)
      simpa using this
    have h3 : ‖y k‖ ^ 2 ≤ (C * ∑ j ∈ Finset.range k, ‖d j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h4 := hsumM k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc ‖y k‖ ^ 2 ≤ C ^ 2 * (∑ j ∈ Finset.range k, ‖d j‖) ^ 2 := by rw [← mul_pow]; exact h3
      _ ≤ C ^ 2 * (k * ∑ j ∈ Finset.range k, ‖d j‖ ^ 2) := by gcongr
      _ ≤ C ^ 2 * (k * M) := by gcongr
      _ = C ^ 2 * k * M := by ring
  -- frequently small
  have hfreq : ∀ n : ℕ, ∃ᶠ k : ℕ in atTop, (k : ℝ) * ‖d k‖ ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra hcon
    rw [not_frequently] at hcon
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    apply Real.not_summable_one_div_natCast
    refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => ‖d k‖ ^ 2 / ε)
      (hsumm.div_const ε) ?_
    filter_upwards [hcon, eventually_ge_atTop 1] with k hk hk1
    push Not at hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [Real.norm_of_nonneg (by positivity), le_div_iff₀ hεpos, div_mul_eq_mul_div, one_mul,
      div_le_iff₀ hkpos]
    linarith
  obtain ⟨sb, hsbmono, hsb⟩ := extraction_forall_of_frequently hfreq
  -- boundedness of X
  set R : ℝ := Real.sqrt (2 * (f xb - G 0)) with hR
  have hXball : ∀ k, X (k + 1) ∈ Metric.closedBall xb R := by
    intro k
    rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub, hR]
    have := hGle xb hxb k
    have := hGmono (Nat.zero_le k)
    rw [← Real.sqrt_sq (norm_nonneg (xb - X (k + 1)))]
    apply Real.sqrt_le_sqrt
    linarith
  obtain ⟨xs, -, ψ, hψmono, hψ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall
    (fun n => hXball (sb n))
  set κ := sb ∘ ψ with hκ
  have hκmono : StrictMono κ := hsbmono.comp hψmono
  have hκt : Tendsto κ atTop atTop := hκmono.tendsto_atTop
  have hXk : Tendsto (fun l => X (κ l + 1)) atTop (𝓝 xs) := hψ
  -- feasibility
  have hfeas : A xs = b := by
    have h1 : Tendsto (fun l => d (κ l)) atTop (𝓝 0) := hd0.comp hκt
    have h2 : Tendsto (fun l => d (κ l)) atTop (𝓝 (b - A xs)) := by
      simp only [hd]
      exact tendsto_const_nhds.sub ((hAc.tendsto xs).comp hXk)
    have := tendsto_nhds_unique h2 h1
    exact (sub_eq_zero.mp this).symm
  -- inner product term along κ tends to zero
  have hyd : Tendsto (fun l => ⟪y (κ l), d (κ l)⟫_ℝ) atTop (𝓝 0) := by
    have hbnd : ∀ l, (‖y (κ l)‖ * ‖d (κ l)‖) ^ 2 ≤ C ^ 2 * M * (1 / ((l : ℝ) + 1)) := by
      intro l
      have h1 := hyb2 (κ l)
      have h2 : ((sb (ψ l) : ℕ) : ℝ) * ‖d (sb (ψ l))‖ ^ 2 < 1 / ((ψ l : ℝ) + 1) := hsb (ψ l)
      have hψl : (l : ℝ) ≤ ψ l := by exact_mod_cast hψmono.id_le l
      have h3 : 1 / ((ψ l : ℝ) + 1) ≤ 1 / ((l : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      have hCM : 0 ≤ C ^ 2 * M := by positivity
      calc (‖y (κ l)‖ * ‖d (κ l)‖) ^ 2 = ‖y (κ l)‖ ^ 2 * ‖d (κ l)‖ ^ 2 := by ring
        _ ≤ (C ^ 2 * (κ l) * M) * ‖d (κ l)‖ ^ 2 := by gcongr
        _ = C ^ 2 * M * ((κ l : ℝ) * ‖d (κ l)‖ ^ 2) := by ring
        _ ≤ C ^ 2 * M * (1 / ((ψ l : ℝ) + 1)) := by
          gcongr
          exact h2.le
        _ ≤ C ^ 2 * M * (1 / ((l : ℝ) + 1)) := by gcongr
    have hlim : Tendsto (fun l : ℕ => C ^ 2 * M * (1 / ((l : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C ^ 2 * M)
      simpa using this
    have hsq : Tendsto (fun l => (‖y (κ l)‖ * ‖d (κ l)‖) ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun l => sq_nonneg _) hbnd hlim
    have hprod : Tendsto (fun l => ‖y (κ l)‖ * ‖d (κ l)‖) atTop (𝓝 0) := by
      have : Tendsto (fun l => Real.sqrt ((‖y (κ l)‖ * ‖d (κ l)‖) ^ 2)) atTop
          (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hsq
      simpa [Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using this
    refine squeeze_zero_norm (fun l => ?_) hprod
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  -- G tends to f xs
  have hGxs : ∀ k, G k + ‖xs - X (k + 1)‖ ^ 2 / 2 ≤ f xs := hGle xs hfeas
  have hGlim : Tendsto G atTop (𝓝 (f xs)) := by
    rw [tendsto_order]
    refine ⟨fun a' ha' => ?_, fun a' ha' => Eventually.of_forall fun k => ?_⟩
    · set η := (f xs - a') / 2 with hη
      have hηpos : 0 < η := by rw [hη]; linarith
      have e1 : ∀ᶠ l in atTop, phi xs - η < phi (X (κ l + 1)) :=
        hXk.eventually (hphi xs (phi xs - η) (by linarith))
      have hcont : Tendsto (fun l => ‖X (κ l + 1)‖ ^ 2 / 2 + ⟪y (κ l), d (κ l)⟫_ℝ) atTop
          (𝓝 (‖xs‖ ^ 2 / 2 + 0)) :=
        (((continuous_norm.tendsto xs).comp hXk).pow 2 |>.div_const 2).add hyd
      have e2 : ∀ᶠ l in atTop, ‖xs‖ ^ 2 / 2 - η < ‖X (κ l + 1)‖ ^ 2 / 2 + ⟪y (κ l), d (κ l)⟫_ℝ :=
        hcont.eventually (lt_mem_nhds (by linarith))
      obtain ⟨l, hl1, hl2⟩ := (e1.and e2).exists
      filter_upwards [eventually_ge_atTop (κ l)] with k hk
      have := hGmono hk
      have hGl : G (κ l) = phi (X (κ l + 1)) + (‖X (κ l + 1)‖ ^ 2 / 2 + ⟪y (κ l), d (κ l)⟫_ℝ) := by
        simp only [hG, hLg, hf, hd]; ring
      simp only [hf] at hη
      linarith
    · have := hGxs k; have : 0 ≤ ‖xs - X (k + 1)‖ ^ 2 / 2 := by positivity
      linarith
  have hXlim1 : Tendsto (fun k => X (k + 1)) atTop (𝓝 xs) := by
    have h1 : Tendsto (fun k => ‖xs - X (k + 1)‖ ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun k => 2 * (f xs - G k)) atTop (𝓝 (2 * (f xs - f xs))) :=
        (tendsto_const_nhds.sub hGlim).const_mul 2
      rw [sub_self, mul_zero] at h2
      refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) h2
      have := hGxs k; linarith
    have h3 : Tendsto (fun k => ‖X (k + 1) - xs‖) atTop (𝓝 0) := by
      have : Tendsto (fun k => Real.sqrt (‖xs - X (k + 1)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp h1
      simpa [Real.sqrt_sq (norm_nonneg _), norm_sub_rev] using this
    exact tendsto_iff_norm_sub_tendsto_zero.mpr h3
  refine ⟨xs, hfeas, (tendsto_add_atTop_iff_nat 1).mp hXlim1, fun W hW => ?_⟩
  have hlim : Tendsto (fun k => G k + ‖W - X (k + 1)‖ ^ 2 / 2) atTop
      (𝓝 (f xs + ‖W - xs‖ ^ 2 / 2)) :=
    hGlim.add ((((continuous_norm.tendsto _).comp (tendsto_const_nhds.sub hXlim1)).pow 2).div_const 2)
  have := le_of_tendsto' hlim (fun k => hGle W hW k)
  simp only [hf] at this
  linarith

end AuxAbstract

section AuxBessel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bessel property of a finite family. -/
def aux_ucv_Bes {ι : Type} [Fintype ι] (p : ι → E) : Prop :=
  ∀ x : E, ∑ i, ⟪p i, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2

theorem aux_ucv_bes_of_orth {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → E)
    (horth : ∀ i j, i ≠ j → ⟪p i, p j⟫_ℝ = 0) (hn : ∀ i, ‖p i‖ ≤ 1) : aux_ucv_Bes p := by
  intro x
  set c : ι → ℝ := fun i => ⟪p i, x⟫_ℝ with hc
  have h1 : ⟪x, ∑ i, c i • p i⟫_ℝ = ∑ i, c i ^ 2 := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, real_inner_comm, sq]
  have h2 : ‖∑ i, c i • p i‖ ^ 2 = ∑ i, c i ^ 2 * ‖p i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
    · intro j _ hji
      rw [real_inner_smul_left, real_inner_smul_right, horth i j (Ne.symm hji)]; ring
    · simp
  have h3 : ∑ i, c i ^ 2 * ‖p i‖ ^ 2 ≤ ∑ i, c i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have : ‖p i‖ ^ 2 ≤ 1 := by
      have := hn i
      have h0 := norm_nonneg (p i)
      nlinarith
    have := sq_nonneg (c i)
    nlinarith
  have h4 := norm_sub_sq_real x (∑ i, c i • p i)
  have h5 : 0 ≤ ‖x - ∑ i, c i • p i‖ ^ 2 := sq_nonneg _
  show ∑ i, c i ^ 2 ≤ ‖x‖ ^ 2
  linarith

theorem aux_ucv_bes_smul {ι : Type} [Fintype ι] (p : ι → E) (hp : aux_ucv_Bes p) (s : ι → ℝ)
    (hs : ∀ i, |s i| ≤ 1) : aux_ucv_Bes (fun i => s i • p i) := by
  intro x
  refine le_trans ?_ (hp x)
  apply Finset.sum_le_sum
  intro i _
  rw [real_inner_smul_left, mul_pow]
  have : s i ^ 2 ≤ 1 := by
    have := hs i
    rw [← sq_abs]
    have h0 := abs_nonneg (s i)
    nlinarith
  have := sq_nonneg ⟪p i, x⟫_ℝ
  nlinarith

theorem aux_ucv_bes_cs {ι : Type} [Fintype ι] {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (p : ι → E) (q : ι → F) (hp : aux_ucv_Bes p) (hq : aux_ucv_Bes q)
    (x : E) (z : F) : ∑ i, ⟪p i, x⟫_ℝ * ⟪q i, z⟫_ℝ ≤ ‖x‖ * ‖z‖ := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have h1 : Real.sqrt (∑ i, ⟪p i, x⟫_ℝ ^ 2) ≤ ‖x‖ := by
    rw [← Real.sqrt_sq (norm_nonneg x)]; exact Real.sqrt_le_sqrt (hp x)
  have h2 : Real.sqrt (∑ i, ⟪q i, z⟫_ℝ ^ 2) ≤ ‖z‖ := by
    rw [← Real.sqrt_sq (norm_nonneg z)]; exact Real.sqrt_le_sqrt (hq z)
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (norm_nonneg _)

theorem aux_ucv_bes_orthonormal {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → E)
    (hp : Orthonormal ℝ p) : aux_ucv_Bes p :=
  aux_ucv_bes_of_orth p (fun i j hij => hp.2 hij) (fun i => (hp.1 i).le)

end AuxBessel

section AuxEigen

open Matrix

variable {n₁ n₂ : ℕ}

theorem aux_ucv_nuc_eq (W : Mat n₁ n₂) :
    nuclearNorm W = ∑ j, ‖Matrix.toEuclideanLin W
      ((Matrix.toEuclideanLin W).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j)‖ := by
  set T := Matrix.toEuclideanLin W with hT
  set hS := T.isSymmetric_adjoint_comp_self
  have key : ∀ j, ‖T (hS.eigenvectorBasis rfl j)‖ = Real.sqrt (hS.eigenvalues rfl j) := by
    intro j
    set e := hS.eigenvectorBasis rfl j
    have h1 : ‖T e‖ ^ 2 = hS.eigenvalues rfl j := by
      rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_right]
      have : LinearMap.adjoint T (T e) = (LinearMap.adjoint T ∘ₗ T) e := rfl
      rw [this, hS.apply_eigenvectorBasis, real_inner_smul_right, real_inner_self_eq_norm_sq,
        (hS.eigenvectorBasis rfl).orthonormal.1 j]
      simp
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  simp only [key]
  unfold nuclearNorm LinearMap.singularValues
  rw [Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [Finsupp.ofSupportFinite_coe]

theorem aux_ucv_orthT (W : Mat n₁ n₂) (j k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂))))
    (hjk : j ≠ k) :
    ⟪Matrix.toEuclideanLin W
        ((Matrix.toEuclideanLin W).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j),
      Matrix.toEuclideanLin W
        ((Matrix.toEuclideanLin W).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl k)⟫_ℝ = 0 := by
  set T := Matrix.toEuclideanLin W with hT
  set hS := T.isSymmetric_adjoint_comp_self
  rw [← LinearMap.adjoint_inner_right]
  have : LinearMap.adjoint T (T (hS.eigenvectorBasis rfl k)) =
      (LinearMap.adjoint T ∘ₗ T) (hS.eigenvectorBasis rfl k) := rfl
  rw [this, hS.apply_eigenvectorBasis, real_inner_smul_right,
    (hS.eigenvectorBasis rfl).orthonormal.2 hjk]
  simp

theorem aux_ucv_F2 (W : Mat n₁ n₂) {ι : Type} [Fintype ι] (p : ι → EuclideanSpace ℝ (Fin n₂))
    (q : ι → EuclideanSpace ℝ (Fin n₁)) (hp : aux_ucv_Bes p) (hq : aux_ucv_Bes q) :
    ∑ i, ⟪q i, Matrix.toEuclideanLin W (p i)⟫_ℝ ≤ nuclearNorm W := by
  set T := Matrix.toEuclideanLin W with hT
  set e := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with he
  have hexp : ∀ i, ⟪q i, T (p i)⟫_ℝ = ∑ j, ⟪p i, e j⟫_ℝ * ⟪q i, T (e j)⟫_ℝ := by
    intro i
    conv_lhs => rw [← e.sum_repr' (p i)]
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, real_inner_smul_right, real_inner_comm]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_comm, aux_ucv_nuc_eq]
  apply Finset.sum_le_sum
  intro j _
  have := aux_ucv_bes_cs p q hp hq (e j) (T (e j))
  rw [e.orthonormal.1 j, one_mul] at this
  exact this

theorem aux_ucv_F1 (W : Mat n₁ n₂) :
    ∃ (p : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂))) → EuclideanSpace ℝ (Fin n₂))
      (q : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂))) → EuclideanSpace ℝ (Fin n₁)),
      aux_ucv_Bes p ∧ aux_ucv_Bes q ∧
        nuclearNorm W = ∑ j, ⟪q j, Matrix.toEuclideanLin W (p j)⟫_ℝ := by
  set T := Matrix.toEuclideanLin W with hT
  set e := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with he
  refine ⟨e, fun j => ‖T (e j)‖⁻¹ • T (e j), aux_ucv_bes_orthonormal _ e.orthonormal, ?_, ?_⟩
  · apply aux_ucv_bes_of_orth
    · intro i j hij
      rw [real_inner_smul_left, real_inner_smul_right, aux_ucv_orthT W i j hij]; ring
    · intro j
      rw [norm_smul, norm_inv, norm_norm]
      by_cases h : ‖T (e j)‖ = 0
      · rw [h]; simp
      · rw [inv_mul_cancel₀ h]
  · rw [aux_ucv_nuc_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    by_cases h : ‖T (e j)‖ = 0
    · rw [h]; simp
    · field_simp
      rfl

theorem aux_ucv_lsc_of {α : Type} [TopologicalSpace α] (f : α → ℝ)
    (h : ∀ x₀, ∃ g : α → ℝ, Continuous g ∧ (∀ x, g x ≤ f x) ∧ g x₀ = f x₀) :
    LowerSemicontinuous f := by
  intro x₀ y hy
  obtain ⟨g, hg, hle, heq⟩ := h x₀
  have : ∀ᶠ x in 𝓝 x₀, y < g x := hg.continuousAt.eventually (lt_mem_nhds (heq ▸ hy))
  exact this.mono fun x hx => hx.trans_le (hle x)

theorem aux_ucv_cont_inner (p : EuclideanSpace ℝ (Fin n₂)) (q : EuclideanSpace ℝ (Fin n₁)) :
    Continuous (fun W : Mat n₁ n₂ => ⟪q, Matrix.toEuclideanLin W p⟫_ℝ) := by
  let Λ : Mat n₁ n₂ →ₗ[ℝ] ℝ :=
    (innerₛₗ ℝ q) ∘ₗ (LinearMap.applyₗ p) ∘ₗ (Matrix.toEuclideanLin).toLinearMap
  exact Λ.continuous_of_finiteDimensional

theorem aux_ucv_nuc_lsc : LowerSemicontinuous (nuclearNorm : Mat n₁ n₂ → ℝ) := by
  apply aux_ucv_lsc_of
  intro X₀
  obtain ⟨p, q, hp, hq, heq⟩ := aux_ucv_F1 X₀
  refine ⟨fun W => ∑ j, ⟪q j, Matrix.toEuclideanLin W (p j)⟫_ℝ, ?_, fun W => aux_ucv_F2 W p q hp hq,
    heq.symm⟩
  exact continuous_finsetSum _ fun j _ => aux_ucv_cont_inner (p j) (q j)

/-- The `i`-th column of a matrix, as a vector of Euclidean space. -/
def aux_ucv_col {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (i : Fin r) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun a => U a i)

theorem aux_ucv_col_orth {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    Orthonormal ℝ (aux_ucv_col U) := by
  rw [orthonormal_iff_ite]
  intro i j
  have := congrFun (congrFun hU j) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
  simp only [aux_ucv_col, EuclideanSpace.inner_toLp_toLp, dotProduct, star_trivial]
  rw [this]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem aux_ucv_entry {r : ℕ} (U : Matrix (Fin n₁) (Fin r) ℝ) (d : Fin r → ℝ)
    (V : Matrix (Fin n₂) (Fin r) ℝ) (a : Fin n₁) (b : Fin n₂) :
    (U * Matrix.diagonal d * Vᵀ) a b = ∑ i, U a i * d i * V b i := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

theorem aux_ucv_DL {r : ℕ} (U : Matrix (Fin n₁) (Fin r) ℝ) (d : Fin r → ℝ)
    (V : Matrix (Fin n₂) (Fin r) ℝ) (x : EuclideanSpace ℝ (Fin n₂)) :
    Matrix.toEuclideanLin (U * Matrix.diagonal d * Vᵀ) x =
      ∑ i, (d i * ⟪aux_ucv_col V i, x⟫_ℝ) • aux_ucv_col U i := by
  ext a
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, aux_ucv_entry, aux_ucv_col,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem aux_ucv_KI {r : ℕ} (U : Matrix (Fin n₁) (Fin r) ℝ) (c : Fin r → ℝ)
    (V : Matrix (Fin n₂) (Fin r) ℝ) (W : Mat n₁ n₂) :
    frobInner (U * Matrix.diagonal c * Vᵀ) W =
      ∑ i, c i * ⟪aux_ucv_col U i, Matrix.toEuclideanLin W (aux_ucv_col V i)⟫_ℝ := by
  simp only [frobInner, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, aux_ucv_entry, aux_ucv_col,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ i, ∑ b, U a i * c i * V b i * W a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, U a i * c i * V b i * W a b := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      ring

theorem aux_ucv_shrink (τ : ℝ) (hτ : 0 < τ) (Y X : Mat n₁ n₂) (h : IsShrink τ Y X)
    (W : Mat n₁ n₂) : frobInner (Y - X) (W - X) ≤ τ * nuclearNorm W - τ * nuclearNorm X := by
  obtain ⟨r, U, σ, V, ⟨hU, hV, hσ, hY⟩, hX⟩ := h
  set σ' : Fin r → ℝ := fun i => max (σ i - τ) 0 with hσ'
  set c : Fin r → ℝ := fun i => σ i - σ' i with hc
  have hYX : Y - X = U * diagonal c * Vᵀ := by
    rw [hY, hX, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  have hc0 : ∀ i, 0 ≤ c i ∧ c i ≤ τ := by
    intro i
    have := hσ i
    simp only [hc, hσ']
    by_cases h : σ i - τ ≤ 0
    · rw [max_eq_right h]; constructor <;> linarith
    · push Not at h
      rw [max_eq_left h.le]; constructor <;> linarith
  have hcσ : ∀ i, c i * σ' i = τ * σ' i := by
    intro i
    simp only [hc, hσ']
    by_cases h : σ i - τ ≤ 0
    · rw [max_eq_right h]; ring
    · push Not at h
      rw [max_eq_left h.le]; ring
  have hσ'0 : ∀ i, 0 ≤ σ' i := fun i => le_max_right _ _
  set u := aux_ucv_col U with hu_def
  set v := aux_ucv_col V with hv_def
  have hu : Orthonormal ℝ u := aux_ucv_col_orth U hU
  have hv : Orthonormal ℝ v := aux_ucv_col_orth V hV
  -- (i)
  have hi : frobInner (Y - X) W ≤ τ * nuclearNorm W := by
    rw [hYX, aux_ucv_KI]
    have hs : ∀ i, |c i / τ| ≤ 1 := by
      intro i
      rw [abs_le]
      obtain ⟨h1, h2⟩ := hc0 i
      constructor
      · have : 0 ≤ c i / τ := div_nonneg h1 hτ.le
        linarith
      · rw [div_le_one hτ]; exact h2
    have := aux_ucv_F2 W v (fun i => (c i / τ) • u i) (aux_ucv_bes_orthonormal v hv)
      (aux_ucv_bes_smul u (aux_ucv_bes_orthonormal u hu) _ hs)
    simp only [real_inner_smul_left] at this
    have e : ∑ i, c i * ⟪u i, Matrix.toEuclideanLin W (v i)⟫_ℝ =
        τ * ∑ i, c i / τ * ⟪u i, Matrix.toEuclideanLin W (v i)⟫_ℝ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this hτ.le
  -- (ii)
  have hii : nuclearNorm X ≤ ∑ i, σ' i := by
    obtain ⟨p, q, hp, hq, heq⟩ := aux_ucv_F1 X
    rw [heq]
    have hT : ∀ j, ⟪q j, Matrix.toEuclideanLin X (p j)⟫_ℝ =
        ∑ i, σ' i * (⟪p j, v i⟫_ℝ * ⟪q j, u i⟫_ℝ) := by
      intro j
      rw [hX, aux_ucv_DL, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, real_inner_comm (p j) (v i)]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hT j), Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum]
    have := aux_ucv_bes_cs p q hp hq (v i) (u i)
    rw [hv.1 i, hu.1 i, one_mul] at this
    calc σ' i * ∑ j, ⟪p j, v i⟫_ℝ * ⟪q j, u i⟫_ℝ ≤ σ' i * 1 :=
          mul_le_mul_of_nonneg_left this (hσ'0 i)
      _ = σ' i := mul_one _
  -- (iii)
  have hiii : frobInner (Y - X) X = τ * ∑ i, σ' i := by
    rw [hYX, aux_ucv_KI, ← hu_def, ← hv_def]
    have hTX : ∀ i, Matrix.toEuclideanLin X (v i) = σ' i • u i := by
      intro i
      rw [hX, aux_ucv_DL, Finset.sum_eq_single i]
      · rw [real_inner_self_eq_norm_sq, hv.1 i]; simp [hu_def]
      · intro k _ hki
        rw [hv.2 hki]; simp
      · simp
    simp_rw [hTX, real_inner_smul_right, real_inner_self_eq_norm_sq, hu.1, one_pow, mul_one]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hcσ i
  have hsub : frobInner (Y - X) (W - X) = frobInner (Y - X) W - frobInner (Y - X) X := by
    simp only [frobInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hsub, hiii]
  have := mul_le_mul_of_nonneg_left hii hτ.le
  linarith

end AuxEigen

section AuxTransfer

variable {n₁ n₂ m : ℕ}

/-- The identification of `n₁ × n₂` matrices with Euclidean space. -/
def aux_ucv_e : Mat n₁ n₂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n₁ × Fin n₂) where
  toFun W := WithLp.toLp 2 (fun p => W p.1 p.2)
  invFun v := fun i j => v.ofLp (i, j)
  map_add' W V := rfl
  map_smul' c W := rfl
  left_inv W := rfl
  right_inv v := rfl

theorem aux_ucv_e_apply (W : Mat n₁ n₂) :
    aux_ucv_e W = WithLp.toLp 2 (fun p : Fin n₁ × Fin n₂ => W p.1 p.2) := rfl

theorem aux_ucv_e_inner (W V : Mat n₁ n₂) :
    ⟪aux_ucv_e W, aux_ucv_e V⟫_ℝ = frobInner W V := by
  rw [aux_ucv_e_apply, aux_ucv_e_apply, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, star_trivial, frobInner, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_ucv_e_norm (W : Mat n₁ n₂) : ‖aux_ucv_e W‖ = frobNorm W := by
  rw [frobNorm, ← aux_ucv_e_inner, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The constraint map transported to Euclidean space. -/
noncomputable def aux_ucv_A (Aop : Fin m → Mat n₁ n₂) :
    EuclideanSpace ℝ (Fin n₁ × Fin n₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun v := WithLp.toLp 2 (fun i => ⟪aux_ucv_e (Aop i), v⟫_ℝ)
  map_add' v w := by
    ext i
    simp [inner_add_right]
  map_smul' c v := by
    ext i
    simp [real_inner_smul_right]

theorem aux_ucv_A_e (Aop : Fin m → Mat n₁ n₂) (W : Mat n₁ n₂) :
    aux_ucv_A Aop (aux_ucv_e W) = WithLp.toLp 2 (applyA Aop W) := by
  ext i
  simp [aux_ucv_A, applyA, aux_ucv_e_inner]

theorem aux_ucv_adj (Aop : Fin m → Mat n₁ n₂) (v : EuclideanSpace ℝ (Fin n₁ × Fin n₂))
    (y : EuclideanSpace ℝ (Fin m)) :
    ⟪aux_ucv_A Aop v, y⟫_ℝ = ⟪v, aux_ucv_e (adjA Aop y.ofLp)⟫_ℝ := by
  simp only [adjA, map_sum, map_smul, inner_sum, real_inner_smul_right]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [aux_ucv_A, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]

theorem aux_ucv_normA (Aop : Fin m → Mat n₁ n₂) (W : Mat n₁ n₂) :
    Real.sqrt (∑ i, applyA Aop W i ^ 2) = ‖aux_ucv_A Aop (aux_ucv_e W)‖ := by
  rw [aux_ucv_A_e, EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem aux_ucv_hL (Aop : Fin m → Mat n₁ n₂) (v : EuclideanSpace ℝ (Fin n₁ × Fin n₂)) :
    ‖aux_ucv_A Aop v‖ ≤ opNormA Aop * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  set Ac := LinearMap.toContinuousLinearMap (aux_ucv_A Aop) with hAc
  have hbdd : BddAbove ((fun X => Real.sqrt (∑ i, applyA Aop X i ^ 2)) ''
      {X : Mat n₁ n₂ | frobNorm X = 1}) := by
    refine ⟨‖Ac‖, ?_⟩
    rintro _ ⟨X, hX, rfl⟩
    replace hX : frobNorm X = 1 := hX
    show Real.sqrt (∑ i, applyA Aop X i ^ 2) ≤ ‖Ac‖
    rw [aux_ucv_normA]
    calc ‖aux_ucv_A Aop (aux_ucv_e X)‖ = ‖Ac (aux_ucv_e X)‖ := rfl
      _ ≤ ‖Ac‖ * ‖aux_ucv_e X‖ := Ac.le_opNorm _
      _ = ‖Ac‖ := by rw [aux_ucv_e_norm, hX, mul_one]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set X := aux_ucv_e.symm (‖v‖⁻¹ • v) with hXdef
  have hX1 : frobNorm X = 1 := by
    rw [← aux_ucv_e_norm, hXdef, LinearEquiv.apply_symm_apply, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hnv.ne']
  have hmem : Real.sqrt (∑ i, applyA Aop X i ^ 2) ≤ opNormA Aop := le_csSup hbdd ⟨X, hX1, rfl⟩
  rw [aux_ucv_normA, hXdef, LinearEquiv.apply_symm_apply, map_smul, norm_smul, norm_inv,
    norm_norm] at hmem
  have : ‖aux_ucv_A Aop v‖ = ‖v‖ * (‖v‖⁻¹ * ‖aux_ucv_A Aop v‖) := by field_simp
  rw [this, mul_comm (opNormA Aop)]
  exact mul_le_mul_of_nonneg_left hmem hnv.le

end AuxTransfer

end CaiCandesShen.Convergence

open CaiCandesShen.Convergence
open scoped InnerProductSpace

theorem solution {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ) (Aop : Fin m → Mat n₁ n₂)
    (b : Fin m → ℝ) (hfeas : ∃ X : Mat n₁ n₂, applyA Aop X = b) (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C * opNormA Aop ^ 2 < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hXy : IsUzawaSeq τ Aop b δ X y) :
    (∃! Xs : Mat n₁ n₂, IsSol31 τ Aop b Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol31 τ Aop b Xs → Tendsto X atTop (𝓝 Xs) := by
  obtain ⟨Xb, hXb⟩ := hfeas
  obtain ⟨a, C, ha, hC, hδ⟩ := hδ
  obtain ⟨hy0, hstep⟩ := hXy
  set e := (aux_ucv_e : Mat n₁ n₂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n₁ × Fin n₂)) with he
  set A := aux_ucv_A Aop with hA
  have hcont : Continuous e.symm :=
    LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  set phi : EuclideanSpace ℝ (Fin n₁ × Fin n₂) → ℝ := fun v => τ * nuclearNorm (e.symm v)
    with hphi_def
  have hphi : LowerSemicontinuous phi := by
    intro v₀ t ht
    have h1 : t / τ < nuclearNorm (e.symm v₀) := by
      rw [div_lt_iff₀ hτ, mul_comm]; exact ht
    have h2 := aux_ucv_nuc_lsc (e.symm v₀) (t / τ) h1
    have h3 := (hcont.tendsto v₀).eventually h2
    refine h3.mono fun v hv => ?_
    have hv' : t / τ < nuclearNorm (e.symm v) := hv
    rw [div_lt_iff₀ hτ, mul_comm] at hv'
    exact hv'
  have hfeasA : ∀ W : Mat n₁ n₂, A (e W) = WithLp.toLp 2 b ↔ applyA Aop W = b := by
    intro W
    rw [hA, he, aux_ucv_A_e]
    exact ⟨fun h => congrArg WithLp.ofLp h, fun h => by rw [h]⟩
  have hfτ : ∀ W : Mat n₁ n₂, fτ τ W = phi (e W) + ‖e W‖ ^ 2 / 2 := by
    intro W
    simp only [hphi_def, LinearEquiv.symm_apply_apply, he, aux_ucv_e_norm, fτ]
    ring
  obtain ⟨xs, hxs, hlim, hopt⟩ := aux_ucv_abstract phi hphi A (fun w => e (adjA Aop w.ofLp))
    (aux_ucv_adj Aop) (opNormA Aop) (aux_ucv_hL Aop) (WithLp.toLp 2 b) (e Xb) ((hfeasA Xb).2 hXb)
    δ a C ha hC hδ (fun k => e (X k)) (fun k => WithLp.toLp 2 (y k)) (by rw [hy0]; rfl)
    (by
      intro k W
      have key := aux_ucv_shrink τ hτ _ _ (hstep k).1 (e.symm W)
      have h1 : e (adjA Aop (y k)) - e (X (k + 1)) = e (adjA Aop (y k) - X (k + 1)) :=
        (map_sub e _ _).symm
      have h2 : W - e (X (k + 1)) = e (e.symm W - X (k + 1)) := by
        rw [map_sub, LinearEquiv.apply_symm_apply]
      rw [h1, h2, he, aux_ucv_e_inner]
      simp only [hphi_def]
      rw [← he, LinearEquiv.symm_apply_apply]
      exact key)
    (by
      intro k
      rw [(hstep k).2, hA, aux_ucv_A_e]
      rfl)
  set Xs0 := e.symm xs with hXs0
  have hexs : e Xs0 = xs := LinearEquiv.apply_symm_apply e xs
  have hfeas0 : applyA Aop Xs0 = b := (hfeasA Xs0).1 (by rw [hexs]; exact hxs)
  have hopt' : ∀ W : Mat n₁ n₂, applyA Aop W = b →
      fτ τ Xs0 + ‖e W - xs‖ ^ 2 / 2 ≤ fτ τ W := by
    intro W hW
    have := hopt (e W) ((hfeasA W).2 hW)
    rw [hfτ, hfτ, hexs]
    linarith
  have hsol : IsSol31 τ Aop b Xs0 := by
    refine ⟨hfeas0, fun W hW => ?_⟩
    have := hopt' W hW
    have : 0 ≤ ‖e W - xs‖ ^ 2 / 2 := by positivity
    linarith
  have huniq : ∀ Xs : Mat n₁ n₂, IsSol31 τ Aop b Xs → Xs = Xs0 := by
    intro Xs hXs
    have h1 := hopt' Xs hXs.1
    have h2 := hXs.2 Xs0 hfeas0
    have h3 : ‖e Xs - xs‖ ^ 2 = 0 := by
      have : 0 ≤ ‖e Xs - xs‖ ^ 2 := sq_nonneg _
      linarith
    have h4 : e Xs = xs := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    rw [hXs0, ← h4, LinearEquiv.symm_apply_apply]
  refine ⟨⟨Xs0, hsol, huniq⟩, fun Xs hXs => ?_⟩
  rw [huniq Xs hXs]
  have : Tendsto (fun k => e.symm (e (X k))) atTop (𝓝 (e.symm xs)) := (hcont.tendsto xs).comp hlim
  simpa using this
