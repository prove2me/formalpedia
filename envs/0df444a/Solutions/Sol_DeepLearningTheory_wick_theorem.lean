-- Prove2me | solution 1 for DeepLearningTheory.wick_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T11:37:43.512788+00:00
-- url     : https://prove2.me/submissions/a9c31042-546d-435d-b86c-6fd403c98ce5

import Mathlib
import Definitions.Def_DLT_GaussianIntegrals

/-! a9908763 DeepLearningTheory.wick_theorem (Roberts-Yaida eq. 1.45, Wick/Isserlis).
Route: for a Finset `s` of labels, both `E s = gaussExpect K (∏ a ∈ s, z (μs a))` and the Wick sum
`W s` over involutions with support `s` satisfy the same recursion
`X s = ∑ b ∈ s.erase a₀, K (μs a₀) (μs b) * X ((s.erase a₀).erase b)` (a₀ = min s), with `X ∅ = 1`.
For `E` this is Gaussian integration by parts (Stein) in direction `K a₀` via Mathlib's
`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`; `E ∅ = 1` is the normalization
(eq. 1.30), proved by diagonalizing `K⁻¹` and a volume-preserving orthogonal change of variables.
Strong induction on `s` then specialise to `s = univ`. -/

set_option autoImplicit false

open MeasureTheory Finset Matrix

namespace DeepLearningTheory
namespace WickLib

variable {M N : ℕ}


/-- Pairings of a subset `s`: involutions whose support is exactly `s`. -/
def P (s : Finset (Fin M)) : Finset (Equiv.Perm (Fin M)) :=
  Finset.univ.filter (fun σ => σ * σ = 1 ∧ σ.support = s)

/-- Wick sum over the pairings of `s`. -/
noncomputable def W (c : Fin M → Fin M → ℝ) (s : Finset (Fin M)) : ℝ :=
  ∑ σ ∈ P s, ∏ a ∈ s.filter (fun a => a < σ a), c a (σ a)

lemma mem_P {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)} :
    σ ∈ P s ↔ σ * σ = 1 ∧ σ.support = s := by simp [P]

lemma P_empty : P (∅ : Finset (Fin M)) = {1} := by
  ext σ; simp only [P, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.support_eq_empty_iff, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl; simp

lemma W_empty (c : Fin M → Fin M → ℝ) : W c (∅ : Finset (Fin M)) = 1 := by
  simp [W, P_empty]

lemma P_univ : P (Finset.univ : Finset (Fin M)) = pairings M := by
  ext σ; simp [P, pairings, Finset.eq_univ_iff_forall, Equiv.Perm.mem_support]

lemma invol_apply {σ : Equiv.Perm (Fin M)} (h : σ * σ = 1) (x : Fin M) : σ (σ x) = x := by
  simpa using congrArg (fun τ : Equiv.Perm (Fin M) => τ x) h

/-- Pointwise form of `swap a₀ b * σ` when `σ` pairs `a₀` with `b`. -/
lemma swap_mul_apply_fwd {σ : Equiv.Perm (Fin M)} (h : σ * σ = 1) {a₀ b : Fin M}
    (hb : σ a₀ = b) (x : Fin M) :
    (Equiv.swap a₀ b * σ) x = if x = a₀ ∨ x = b then x else σ x := by
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  rw [Equiv.Perm.mul_apply]
  by_cases hx0 : x = a₀
  · subst hx0; simp [hb]
  by_cases hxb : x = b
  · subst hxb; simp [hσb]
  have h1 : σ x ≠ a₀ := by
    intro h'; apply hxb; rw [← invol_apply h x, h', hb]
  have h2 : σ x ≠ b := by
    intro h'; apply hx0; rw [← hb] at h'; exact σ.injective h'
  simp [hx0, hxb, Equiv.swap_apply_of_ne_of_ne h1 h2]


lemma fwd_mem {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)} (hσ : σ ∈ P s) {a₀ b : Fin M}
    (ha₀ : a₀ ∈ s) (hb : σ a₀ = b) :
    Equiv.swap a₀ b * σ ∈ P ((s.erase a₀).erase b) := by
  rw [mem_P] at hσ ⊢
  obtain ⟨h, hs⟩ := hσ
  have hne : σ a₀ ≠ a₀ := by rw [← Equiv.Perm.mem_support, hs]; exact ha₀
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  have key := swap_mul_apply_fwd h hb
  constructor
  · ext x
    rw [Equiv.Perm.mul_apply, key x, Equiv.Perm.one_apply]
    by_cases hx : x = a₀ ∨ x = b
    · simp [hx, key]
    · rw [if_neg hx, key (σ x)]
      have : ¬ (σ x = a₀ ∨ σ x = b) := by
        rintro (h' | h')
        · apply hx; right; rw [← invol_apply h x, h', hb]
        · apply hx; left; rw [← hb] at h'; exact σ.injective h'
      rw [if_neg this, invol_apply h]
  · ext x
    rw [Equiv.Perm.mem_support, key x, Finset.mem_erase, Finset.mem_erase, ← hs,
      Equiv.Perm.mem_support]
    by_cases hx0 : x = a₀
    · subst hx0; simp
    by_cases hxb : x = b
    · subst hxb; simp
    simp [hx0, hxb]

lemma bwd_mem {s : Finset (Fin M)} {τ : Equiv.Perm (Fin M)} {a₀ b : Fin M}
    (ha₀ : a₀ ∈ s) (hb : b ∈ s.erase a₀) (hτ : τ ∈ P ((s.erase a₀).erase b)) :
    Equiv.swap a₀ b * τ ∈ P s ∧ (Equiv.swap a₀ b * τ) a₀ = b := by
  rw [mem_P] at hτ ⊢
  obtain ⟨h, hs⟩ := hτ
  have hba : b ≠ a₀ := (Finset.mem_erase.1 hb).1
  have hbs : b ∈ s := (Finset.mem_erase.1 hb).2
  have hτa : τ a₀ = a₀ := by
    by_contra hc
    have := Equiv.Perm.mem_support.2 hc; rw [hs] at this; simp at this
  have hτb : τ b = b := by
    by_contra hc
    have := Equiv.Perm.mem_support.2 hc; rw [hs] at this; simp at this
  have hmid : ∀ x, x ≠ a₀ → x ≠ b → τ x ≠ a₀ ∧ τ x ≠ b := by
    intro x h0 h1
    refine ⟨fun h' => h0 (τ.injective (h'.trans hτa.symm)),
      fun h' => h1 (τ.injective (h'.trans hτb.symm))⟩
  have key : ∀ x, (Equiv.swap a₀ b * τ) x = if x = a₀ then b else if x = b then a₀ else τ x := by
    intro x
    rw [Equiv.Perm.mul_apply]
    by_cases h0 : x = a₀
    · subst h0; simp [hτa]
    by_cases h1 : x = b
    · subst h1; simp [hτb, hba]
    obtain ⟨m0, m1⟩ := hmid x h0 h1
    simp [h0, h1, Equiv.swap_apply_of_ne_of_ne m0 m1]
  refine ⟨⟨?_, ?_⟩, by simp [key]⟩
  · ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases h0 : x = a₀
    · subst h0; simp [key, hba]
    by_cases h1 : x = b
    · subst h1; simp [key, hba]
    obtain ⟨m0, m1⟩ := hmid x h0 h1
    rw [key x, if_neg h0, if_neg h1, key (τ x), if_neg m0, if_neg m1, invol_apply h]
  · ext x
    rw [Equiv.Perm.mem_support, key x]
    by_cases h0 : x = a₀
    · subst h0; simp [hba, ha₀]
    by_cases h1 : x = b
    · subst h1; simp [hba, hbs]; exact fun h => hba h.symm
    rw [if_neg h0, if_neg h1, ← Equiv.Perm.mem_support, hs]
    simp [h0, h1]


lemma prod_fwd (c : Fin M → Fin M → ℝ) {s : Finset (Fin M)} {σ : Equiv.Perm (Fin M)}
    (hσ : σ ∈ P s) {a₀ b : Fin M} (ha₀ : a₀ ∈ s) (hmin : ∀ x ∈ s, a₀ ≤ x) (hb : σ a₀ = b) :
    ∏ a ∈ s.filter (fun a => a < σ a), c a (σ a) =
      c a₀ b * ∏ a ∈ ((s.erase a₀).erase b).filter (fun a => a < (Equiv.swap a₀ b * σ) a),
        c a ((Equiv.swap a₀ b * σ) a) := by
  rw [mem_P] at hσ
  obtain ⟨h, hs⟩ := hσ
  have hsupp : a₀ ∈ σ.support := by rw [hs]; exact ha₀
  have hne : σ a₀ ≠ a₀ := Equiv.Perm.mem_support.1 hsupp
  have hbs : b ∈ s.erase a₀ := by
    rw [Finset.mem_erase, ← hb]
    exact ⟨hne, by rw [← hs]; exact Equiv.Perm.apply_mem_support.2 hsupp⟩
  have hab : a₀ < b :=
    lt_of_le_of_ne (hmin b (Finset.mem_of_mem_erase hbs)) (by rw [← hb]; exact hne.symm)
  have hσb : σ b = a₀ := by rw [← hb, invol_apply h]
  have key := swap_mul_apply_fwd h hb
  rw [Finset.prod_filter, Finset.prod_filter]
  conv_lhs => rw [← Finset.insert_erase ha₀, ← Finset.insert_erase hbs]
  rw [Finset.prod_insert (by simp [hab.ne]), Finset.prod_insert (by simp)]
  rw [hb, if_pos hab, hσb, if_neg (not_lt.2 hab.le), one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hxb : x ≠ b := (Finset.mem_erase.1 hx).1
  have hx0 : x ≠ a₀ := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
  have : ¬ (x = a₀ ∨ x = b) := by tauto
  rw [key x, if_neg this]

lemma W_rec (c : Fin M → Fin M → ℝ) {s : Finset (Fin M)} (hs : s.Nonempty) :
    W c s = ∑ b ∈ s.erase (s.min' hs),
      c (s.min' hs) b * W c ((s.erase (s.min' hs)).erase b) := by
  have ha₀ : s.min' hs ∈ s := Finset.min'_mem s hs
  have hmin : ∀ x ∈ s, s.min' hs ≤ x := fun x hx => Finset.min'_le s x hx
  unfold W
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin M) => σ (s.min' hs))
    (t := s.erase (s.min' hs))]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun σ => Equiv.swap (s.min' hs) b * σ)
      (fun τ => Equiv.swap (s.min' hs) b * τ)
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact fwd_mem hσ.1 ha₀ hσ.2
    · intro τ hτ
      obtain ⟨h1, h2⟩ := bwd_mem ha₀ hb hτ
      exact Finset.mem_filter.2 ⟨h1, h2⟩
    · intro σ _; simp [Equiv.swap_mul_self_mul]
    · intro τ _; simp [Equiv.swap_mul_self_mul]
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact prod_fwd c hσ.1 ha₀ hmin hσ.2
  · intro σ hσ
    rw [mem_P] at hσ
    have hsupp : s.min' hs ∈ σ.support := by rw [hσ.2]; exact ha₀
    rw [Finset.mem_erase]
    have h2 := Equiv.Perm.apply_mem_support.2 hsupp
    rw [hσ.2] at h2
    exact ⟨Equiv.Perm.mem_support.1 hsupp, h2⟩



lemma quad_eq_dot (K : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) :
    gaussQuadForm K z = z ⬝ᵥ (K⁻¹ *ᵥ z) := by
  simp [gaussQuadForm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma diag {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) :
    ∃ (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ), (∀ i, 0 < d i) ∧ Uᵀ * U = 1 ∧
      U * Uᵀ = 1 ∧ (∏ i, d i) * K.det = 1 ∧
      ∀ w, gaussQuadForm K (U *ᵥ w) = ∑ i, d i * w i ^ 2 := by
  have hH : K⁻¹.PosDef := hK.inv
  obtain ⟨U, d, hd, hUU, hUU', hdet, hspec⟩ : ∃ (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ),
      (∀ i, 0 < d i) ∧ Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ K⁻¹.det = ∏ i, d i ∧
      K⁻¹ = U * diagonal d * Uᵀ := by
    have hstar : star (hH.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) =
        (hH.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ := by
      rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    refine ⟨hH.1.eigenvectorUnitary, hH.1.eigenvalues, hH.eigenvalues_pos, ?_, ?_, ?_, ?_⟩
    · rw [← hstar]; exact Unitary.coe_star_mul_self hH.1.eigenvectorUnitary
    · rw [← hstar]; exact Unitary.coe_mul_star_self hH.1.eigenvectorUnitary
    · have := hH.1.det_eq_prod_eigenvalues
      simpa only [RCLike.ofReal_real_eq_id, id] using this
    · have := hH.1.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at this
      rw [← hstar]; exact this
  have hdetU : IsUnit K.det := isUnit_iff_ne_zero.2 hK.det_pos.ne'
  refine ⟨U, d, hd, hUU, hUU', ?_, ?_⟩
  · rw [← hdet]
    exact det_nonsing_inv_mul_det (A := K) hdetU
  · intro w
    have h1 : (U *ᵥ w) ᵥ* U = w := by
      rw [← vecMul_transpose, vecMul_vecMul, hUU, vecMul_one]
    rw [quad_eq_dot, hspec, mulVec_mulVec, mul_assoc, mul_assoc, hUU, mul_one,
      ← mulVec_mulVec, dotProduct_mulVec, h1]
    simp [dotProduct, mulVec_diagonal, sq]
    apply Finset.sum_congr rfl; intro i _; ring

lemma coercive {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) :
    ∃ c > 0, ∀ z : Fin N → ℝ, c * ∑ i, z i ^ 2 ≤ gaussQuadForm K z := by
  obtain ⟨U, d, hd, hUU, hUU', -, hq⟩ := diag hK
  obtain ⟨c, hc0, hc⟩ : ∃ c > 0, ∀ i, c ≤ d i := by
    rcases isEmpty_or_nonempty (Fin N) with h | h
    · exact ⟨1, one_pos, fun i => h.elim i⟩
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
      exact ⟨d i₀, hd i₀, fun i => hi₀ i (Finset.mem_univ _)⟩
  refine ⟨c, hc0, fun z => ?_⟩
  have hz : z = U *ᵥ (Uᵀ *ᵥ z) := by rw [mulVec_mulVec, hUU', one_mulVec]
  have hnorm : ∀ w, ∑ i, (U *ᵥ w) i ^ 2 = ∑ i, w i ^ 2 := by
    intro w
    have h1 : (U *ᵥ w) ᵥ* U = w := by
      rw [← vecMul_transpose, vecMul_vecMul, hUU, vecMul_one]
    have h2 : (U *ᵥ w) ⬝ᵥ (U *ᵥ w) = w ⬝ᵥ w := by rw [dotProduct_mulVec, h1]
    simpa [dotProduct, sq] using h2
  rw [hz, hq, hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)


/-- Unnormalised Gaussian weight. -/
noncomputable def eF (K : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * gaussQuadForm K z)

lemma continuous_quad (K : Matrix (Fin N) (Fin N) ℝ) : Continuous (gaussQuadForm K) := by
  unfold gaussQuadForm; fun_prop

lemma continuous_eF (K : Matrix (Fin N) (Fin N) ℝ) : Continuous (eF K) := by
  unfold eF; exact Real.continuous_exp.comp (continuous_const.mul (continuous_quad K))

lemma integral_eF {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) :
    ∫ z, eF K z = Real.sqrt ((2 * Real.pi) ^ N * K.det) := by
  obtain ⟨U, d, hd, hUU, hUU', hdet, hq⟩ := diag hK
  have hdU : U.det * U.det = 1 := by
    have := congrArg det hUU
    rwa [det_mul, det_transpose, det_one] at this
  have habs : |U.det| = 1 := by
    have h2 : |U.det| * |U.det| = 1 := by rw [abs_mul_abs_self]; exact hdU
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · have := abs_nonneg U.det; linarith
  have hdU0 : U.det ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; exact zero_ne_one habs
  have hmap : Measure.map (Matrix.toLin' U) (volume : Measure (Fin N → ℝ)) = volume := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdU0, abs_inv, habs, inv_one,
      ENNReal.ofReal_one, one_smul]
  have hcv : ∫ z, eF K z = ∫ w, eF K (U *ᵥ w) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (Matrix.toLin' U).continuous_of_finiteDimensional.measurable.aemeasurable
      (continuous_eF K).aestronglyMeasurable]
    simp [Matrix.toLin'_apply]
  have hprod : ∀ w, eF K (U *ᵥ w) = ∏ i, Real.exp (-(d i / 2) * w i ^ 2) := by
    intro w
    rw [eF, hq, ← Real.exp_sum, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [hcv]
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) => Real.exp (-(d i / 2) * x ^ 2))]
  simp_rw [integral_gaussian]
  rw [← Real.sqrt_prod _ (fun i _ => div_nonneg Real.pi_pos.le (by linarith [hd i]))]
  congr 1
  have hdetK : K.det = (∏ i, d i)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have h1 : ∀ i, Real.pi / (d i / 2) = (2 * Real.pi) * (d i)⁻¹ := by
    intro i; have := (hd i).ne'; field_simp
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_inv_distrib, hdetK]


lemma integrable_one_add_abs_pow_mul_exp {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ k * Real.exp (-b * x ^ 2)) := by
  have h : ∀ x : ℝ, (1 + |x|) ^ k * Real.exp (-b * x ^ 2) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (|x| ^ j * Real.exp (-b * x ^ 2)) := by
    intro x
    rw [add_comm, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; simp only [one_pow, mul_one]; ring
  simp_rw [h]
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  have := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (j : ℝ))
    (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast, abs_of_pos (Real.exp_pos _)]

lemma abs_le_prod_one_add (z : Fin N → ℝ) (j : Fin N) : |z j| ≤ ∏ i, (1 + |z i|) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => 1 + |z i|) (Finset.mem_univ j)]
  have h1 : 1 ≤ ∏ i ∈ Finset.univ.erase j, (1 + |z i|) :=
    Finset.one_le_prod (fun i _ => by linarith [abs_nonneg (z i)])
  nlinarith [abs_nonneg (z j)]

lemma abs_mono_le {ι : Type*} (t : Finset ι) (ν : ι → Fin N) (z : Fin N → ℝ) :
    |∏ a ∈ t, z (ν a)| ≤ ∏ i, (1 + |z i|) ^ t.card := by
  rw [Finset.abs_prod, Finset.prod_pow, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun a _ => abs_nonneg _) (fun a _ => abs_le_prod_one_add z (ν a))

lemma integrable_mono_eF {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) {ι : Type*}
    (t : Finset ι) (ν : ι → Fin N) :
    Integrable (fun z => eF K z * ∏ a ∈ t, z (ν a)) := by
  obtain ⟨c, hc0, hc⟩ := coercive hK
  have hdom : Integrable (fun z : Fin N → ℝ =>
      ∏ i, ((1 + |z i|) ^ t.card * Real.exp (-(c / 2) * z i ^ 2))) := by
    have := Integrable.fintype_prod
      (f := fun (_ : Fin N) (x : ℝ) => (1 + |x|) ^ t.card * Real.exp (-(c / 2) * x ^ 2))
      (μ := fun _ => volume)
      (fun _ => integrable_one_add_abs_pow_mul_exp (by positivity) t.card)
    simpa [← volume_pi] using this
  refine hdom.mono' ((continuous_eF K).mul (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, eF, abs_of_pos (Real.exp_pos _), Finset.prod_mul_distrib,
    mul_comm]
  apply mul_le_mul (abs_mono_le t ν z) _ (Real.exp_pos _).le
    (Finset.prod_nonneg fun i _ => pow_nonneg (by linarith [abs_nonneg (z i)]) _)
  rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
  have := hc z
  nlinarith


lemma hasDerivAt_quad (K : Matrix (Fin N) (Fin N) ℝ) (z v : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ μ, ∑ ν, (z μ + t * v μ) * K⁻¹ μ ν * (z ν + t * v ν))
      (∑ μ, ∑ ν, (v μ * K⁻¹ μ ν * z ν + z μ * K⁻¹ μ ν * v ν)) 0 := by
  apply HasDerivAt.fun_sum; intro μ _; apply HasDerivAt.fun_sum; intro ν _
  have h1 : ∀ j, HasDerivAt (fun t : ℝ => z j + t * v j) (v j) 0 := by
    intro j
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (z j)
  refine (((h1 μ).mul_const (K⁻¹ μ ν)).mul (h1 ν)).congr_deriv ?_
  simp

lemma hasLineDerivAt_eF {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) (i : Fin N)
    (z : Fin N → ℝ) :
    HasLineDerivAt ℝ (eF K) (-(z i) * eF K z) z (fun j => K i j) := by
  have hdetU : IsUnit K.det := isUnit_iff_ne_zero.2 hK.det_pos.ne'
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hdetU
  have hKK' : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hdetU
  have hsym : ∀ a b, K a b = K b a := fun a b => by
    have := hK.1.apply a b
    simpa using this.symm
  have e1 : ∑ μ, ∑ ν, K i μ * K⁻¹ μ ν * z ν = z i := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Matrix.mul_apply, hKK, Matrix.one_apply]
    simp
  have e2 : ∑ μ, ∑ ν, z μ * K⁻¹ μ ν * K i ν = z i := by
    have : ∀ μ, ∑ ν, z μ * K⁻¹ μ ν * K i ν = z μ * (K⁻¹ * K) μ i := by
      intro μ
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ν _; rw [hsym i ν]; ring
    simp_rw [this, hKK', Matrix.one_apply]
    simp
  have h0 := ((hasDerivAt_quad K z (fun j => K i j)).const_mul (-(1 / 2 : ℝ))).exp
  have h1 : HasDerivAt (fun t : ℝ => eF K (z + t • fun j => K i j))
      (Real.exp (-(1 / 2) * ∑ μ, ∑ ν, (z μ + 0 * K i μ) * K⁻¹ μ ν * (z ν + 0 * K i ν)) *
        (-(1 / 2) * ∑ μ, ∑ ν, (K i μ * K⁻¹ μ ν * z ν + z μ * K⁻¹ μ ν * K i ν))) 0 := h0
  refine h1.congr_deriv ?_
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_add_distrib), Finset.sum_add_distrib, e1, e2]
  simp only [zero_mul, add_zero, eF, gaussQuadForm]
  ring

lemma hasLineDerivAt_mono {ι : Type*} [DecidableEq ι] (t : Finset ι) (ν : ι → Fin N)
    (z v : Fin N → ℝ) :
    HasLineDerivAt ℝ (fun z : Fin N → ℝ => ∏ a ∈ t, z (ν a))
      (∑ b ∈ t, v (ν b) * ∏ a ∈ t.erase b, z (ν a)) z v := by
  have := HasDerivAt.fun_finsetProd (u := t) (f := fun a (τ : ℝ) => z (ν a) + τ * v (ν a))
    (f' := fun a => v (ν a)) (x := 0) (fun a _ => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v (ν a))).const_add (z (ν a)))
  have h1 : HasDerivAt (fun τ : ℝ => ∏ a ∈ t, (z + τ • v) (ν a))
      (∑ i ∈ t, (∏ j ∈ t.erase i, (z (ν j) + 0 * v (ν j))) • v (ν i)) 0 := this
  refine h1.congr_deriv ?_
  simp [mul_comm]

lemma stein {M : ℕ} {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) (μs : Fin M → Fin N)
    {s : Finset (Fin M)} {a₀ : Fin M} (ha₀ : a₀ ∈ s) :
    ∫ z, eF K z * ∏ a ∈ s, z (μs a) =
      ∑ b ∈ s.erase a₀, K (μs a₀) (μs b) * ∫ z, eF K z * ∏ a ∈ (s.erase a₀).erase b, z (μs a) := by
  have hsplit : ∀ z : Fin N → ℝ, ∏ a ∈ s, z (μs a) = z (μs a₀) * ∏ a ∈ s.erase a₀, z (μs a) :=
    fun z => (Finset.mul_prod_erase s (fun a => z (μs a)) ha₀).symm
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin N → ℝ))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := eF K) (f' := fun z => -(z (μs a₀)) * eF K z)
    (g := fun z => ∏ a ∈ s.erase a₀, z (μs a))
    (g' := fun z => ∑ b ∈ s.erase a₀, K (μs a₀) (μs b) * ∏ a ∈ (s.erase a₀).erase b, z (μs a))
    (v := fun j => K (μs a₀) j) ?_ ?_ ?_
    (fun z _ => hasLineDerivAt_eF hK (μs a₀) z)
    (fun z _ => hasLineDerivAt_mono (s.erase a₀) μs z _)
  · simp only [ContinuousLinearMap.mul_apply'] at hibp
    have hL : ∫ z, eF K z * ∏ a ∈ s, z (μs a) =
        -∫ z, -(z (μs a₀)) * eF K z * ∏ a ∈ s.erase a₀, z (μs a) := by
      rw [← integral_neg]
      congr 1; funext z; rw [hsplit]; ring
    rw [hL, ← hibp]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl; intro b _
      rw [← integral_const_mul]
      congr 1; funext z; ring
    · intro b _
      exact ((integrable_mono_eF hK _ μs).const_mul (K (μs a₀) (μs b))).congr
        (Filter.Eventually.of_forall fun z => by simp only; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact (integrable_mono_eF hK s μs).neg.congr
      (Filter.Eventually.of_forall fun z => by simp only [Pi.neg_apply]; rw [hsplit]; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro b _
    exact ((integrable_mono_eF hK _ μs).const_mul (K (μs a₀) (μs b))).congr
      (Filter.Eventually.of_forall fun z => by simp only; ring)
  · simp only [ContinuousLinearMap.mul_apply']
    exact integrable_mono_eF hK _ μs

lemma gaussExpect_eq (K : Matrix (Fin N) (Fin N) ℝ) (F : (Fin N → ℝ) → ℝ) :
    gaussExpect K F = (Real.sqrt ((2 * Real.pi) ^ N * K.det))⁻¹ * ∫ z, eF K z * F z := by
  unfold gaussExpect gaussianDensity eF
  rw [← integral_const_mul]
  congr 1; funext z; ring

lemma wick_aux {M : ℕ} {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) (μs : Fin M → Fin N)
    (s : Finset (Fin M)) :
    gaussExpect K (fun z => ∏ a ∈ s, z (μs a)) = W (fun a b => K (μs a) (μs b)) s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [W_empty, gaussExpect_eq]
      simp only [Finset.prod_empty, mul_one]
      rw [integral_eF hK]
      apply inv_mul_cancel₀
      rw [Real.sqrt_ne_zero']
      exact mul_pos (pow_pos (by positivity) _) hK.det_pos
    · rw [W_rec _ hs, gaussExpect_eq, stein hK μs (Finset.min'_mem s hs), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hsub : (s.erase (s.min' hs)).erase b ⊂ s :=
        (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset (Finset.min'_mem s hs))
      rw [← ih _ hsub, gaussExpect_eq]
      ring

end WickLib
end DeepLearningTheory

set_option maxHeartbeats 4000000 in
open MeasureTheory DeepLearningTheory in
theorem solution {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.PosDef)
    (m : ℕ) (μs : Fin (2 * m) → Fin N) :
    gaussExpect K (fun z => ∏ a : Fin (2 * m), z (μs a))
      = ∑ σ ∈ pairings (2 * m),
          ∏ a ∈ Finset.univ.filter (fun a : Fin (2 * m) => a < σ a), K (μs a) (μs (σ a)) := by
  have := WickLib.wick_aux hK μs Finset.univ
  rw [WickLib.W, WickLib.P_univ] at this
  exact this
