-- Prove2me | solution 1 for DirichletUnitTheorem.cyclic_cubic_fundamental_units
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:04:31.888385+00:00
-- url     : https://prove2.me/submissions/6ce29a8c-110e-4d87-aaa7-ef1e964e8e3d

import Mathlib
open NumberField

def ccP (a b c : ℤ) : ℤ := a^3+4*a*a*b-a*a*c+3*a*b*b-5*a*b*c-2*a*c*c-b^3-b*b*c+2*b*c*c+c^3

set_option maxRecDepth 100000 in
theorem ccDec : ∀ a ∈ Finset.Icc (-5:ℤ) 5, ∀ b ∈ Finset.Icc (-6:ℤ) 6, ∀ c ∈ Finset.Icc (-8:ℤ) 8,
    (ccP a b c = 49 ∨ ccP a b c = -49) →
    (a, b, c) ∈ ([(-5, -3, -6), (-5, 4, -6), (-5, 4, 1), (-4, -1, -2), (-4, -1, 5), (-3, -6, -5), (-3, 1, -5), (-3, 1, 2), (-2, -4, -1), (-2, 3, -8), (-2, 3, -1), (-1, -2, -4), (-1, -2, 3), (-1, 5, -4), (-1, 5, 3), (1, -5, -3), (1, -5, 4), (1, 2, -3), (1, 2, 4), (2, -3, 1), (2, -3, 8), (2, 4, 1), (3, -1, -2), (3, -1, 5), (3, 6, 5), (4, 1, -5), (4, 1, 2), (5, -4, -1), (5, -4, 6), (5, 3, 6)] : List (ℤ × ℤ × ℤ)) := by
  decide +kernel


namespace CCAux

/-- the real root `2cos(2π/7)` -/
lemma exists_root : ∃ r : ℝ, r ^ 3 + r ^ 2 - 2 * r - 1 = 0 ∧
    (1.24697960 : ℝ) < r ∧ r < 1.24697961 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + x ^ 2 - 2 * x - 1) (Set.Icc 1.24697960 1.24697961) :=
    by fun_prop
  have := intermediate_value_Ioo (by norm_num) hc
  obtain ⟨r, ⟨h1, h2⟩, h3⟩ := this (show (0:ℝ) ∈ Set.Ioo _ _ by
    simp only [Set.mem_Ioo]; norm_num)
  exact ⟨r, h3, h1, h2⟩

lemma factor (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (z : ℂ) :
    z ^ 3 + z ^ 2 - 2 * z - 1 = (z - r) * (z - (r ^ 2 - 2 : ℝ)) * (z - (1 - r - r ^ 2 : ℝ)) := by
  have hr' : (r : ℂ) ^ 3 + (r : ℂ) ^ 2 - 2 * r - 1 = 0 := by exact_mod_cast hr
  push_cast
  linear_combination (-(r:ℂ) ^ 2 + r * z + 1) * hr'

variable {K : Type*} [Field K] [NumberField K]

lemma not_rat (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (h1 : (1.24697960 : ℝ) < r)
    (h2 : r < 1.24697961) (α : K) (hα : α ^ 3 + α ^ 2 - 2 * α - 1 = 0) (q : ℚ) :
    algebraMap ℚ K q ≠ α := by
  intro hq
  have hq3 : q ^ 3 + q ^ 2 - 2 * q - 1 = 0 := by
    apply (algebraMap ℚ K).injective
    simp only [map_sub, map_add, map_pow, map_mul, map_ofNat, map_one, map_zero, hq, hα]
  have hint : IsIntegral ℤ q := by
    refine ⟨Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1, ?_, ?_⟩
    · monicity!
    · simp [hq3]
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hn' : (q : ℂ) = (n : ℂ) := by rw [← hn]; simp
  have hz : ((n : ℝ) : ℂ) ^ 3 + ((n : ℝ) : ℂ) ^ 2 - 2 * ((n : ℝ) : ℂ) - 1 = 0 := by
    have : (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - 2 * q - 1 = 0 := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) hq3
    rw [hn'] at this; exact_mod_cast this
  rw [factor r hr] at hz
  have hr2 : (1 - r - r ^ 2 : ℝ) < -1 := by nlinarith
  have hr3 : -1 < (r ^ 2 - 2 : ℝ) ∧ (r ^ 2 - 2 : ℝ) < 0 := by constructor <;> nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · have : (n : ℝ) = r := by exact_mod_cast sub_eq_zero.mp h
      have a1 : (1 : ℝ) < n := by linarith
      have a2 : (n : ℝ) < 2 := by linarith
      have : (1 : ℤ) < n := by exact_mod_cast a1
      have : n < (2 : ℤ) := by exact_mod_cast a2
      omega
    · have : (n : ℝ) = r ^ 2 - 2 := by exact_mod_cast sub_eq_zero.mp h
      have a1 : (-1 : ℝ) < n := by linarith
      have a2 : (n : ℝ) < 0 := by linarith
      have : (-1 : ℤ) < n := by exact_mod_cast a1
      have : n < (0 : ℤ) := by exact_mod_cast a2
      omega
  · have : (n : ℝ) = 1 - r - r ^ 2 := by exact_mod_cast sub_eq_zero.mp h
    have a1 : (-2 : ℝ) < n := by nlinarith
    have a2 : (n : ℝ) < -1 := by linarith
    have : (-2 : ℤ) < n := by exact_mod_cast a1
    have : n < (-1 : ℤ) := by exact_mod_cast a2
    omega

lemma adjoin_top (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (h1 : (1.24697960 : ℝ) < r)
    (h2 : r < 1.24697961) (hK : Module.finrank ℚ K = 3) (α : K)
    (hα : α ^ 3 + α ^ 2 - 2 * α - 1 = 0) : Algebra.adjoin ℚ {α} = ⊤ := by
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have htow := Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {α}) K
  rw [hK] at htow
  have hdvd : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) ∣ 3 := Dvd.intro _ htow
  have hF : IntermediateField.adjoin ℚ {α} = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso
      rw [IntermediateField.finrank_eq_one_iff] at h
      have hm : α ∈ (⊥ : IntermediateField ℚ K) := h ▸ IntermediateField.mem_adjoin_simple_self ℚ α
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hm
      exact not_rat r hr h1 h2 α hα q hq
    · apply IntermediateField.eq_of_le_of_finrank_eq le_top
      rw [h, IntermediateField.finrank_top', hK]
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hF]
  rfl


/-- the three real roots, as polynomials in `r` -/
def ρ (r : ℝ) : Fin 3 → ℝ := ![r, r ^ 2 - 2, 1 - r - r ^ 2]

lemma root_cases (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (z : ℂ)
    (hz : z ^ 3 + z ^ 2 - 2 * z - 1 = 0) : ∃ k, z = (ρ r k : ℂ) := by
  rw [factor r hr] at hz
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by simpa [ρ] using sub_eq_zero.mp h⟩
    · exact ⟨1, by simpa [ρ] using sub_eq_zero.mp h⟩
  · exact ⟨2, by simpa [ρ] using sub_eq_zero.mp h⟩

/-- a complex embedding with real values, as a real embedding -/
def toReal (φ : K →+* ℂ) (h : ∀ x, (φ x).im = 0) : K →+* ℝ where
  toFun x := (φ x).re
  map_one' := by simp
  map_mul' x y := by simp [Complex.mul_re, h]
  map_zero' := by simp
  map_add' x y := by simp

lemma toReal_coe (φ : K →+* ℂ) (h : ∀ x, (φ x).im = 0) (x : K) :
    ((toReal φ h x : ℝ) : ℂ) = φ x := Complex.ext rfl (by simp [h])

lemma setup (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (h1 : (1.24697960 : ℝ) < r)
    (h2 : r < 1.24697961) (hK : Module.finrank ℚ K = 3) (α : K)
    (hα : α ^ 3 + α ^ 2 - 2 * α - 1 = 0) :
    ∃ σ : Fin 3 → (K →+* ℝ), (∀ k, σ k α = ρ r k) ∧
      (∀ x, ((Algebra.trace ℚ K x : ℚ) : ℝ) = ∑ k, σ k x) ∧
      (∀ x, ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ k, σ k x) := by
  classical
  have htop := adjoin_top r hr h1 h2 hK α hα
  have hroot : ∀ φ : K →ₐ[ℚ] ℂ, ∃ k, φ α = (ρ r k : ℂ) := fun φ =>
    root_cases r hr _ (by
      have := congrArg φ hα
      simpa only [map_sub, map_add, map_pow, map_mul, map_ofNat, map_one, map_zero] using this)
  let g : (K →ₐ[ℚ] ℂ) → Fin 3 := fun φ => (hroot φ).choose
  have hg : ∀ φ, φ α = (ρ r (g φ) : ℂ) := fun φ => (hroot φ).choose_spec
  have ginj : Function.Injective g := by
    intro φ ψ h
    apply AlgHom.ext_of_adjoin_eq_top htop
    intro x hx
    rw [Set.mem_singleton_iff.mp hx, hg, hg, h]
  have gbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨ginj, ?_⟩
    rw [AlgHom.card, hK, Fintype.card_fin]
  let e := (Equiv.ofBijective g gbij).symm
  have he : ∀ k, e k α = (ρ r k : ℂ) := by
    intro k
    have := hg (e k)
    rwa [show g (e k) = k from (Equiv.ofBijective g gbij).apply_symm_apply k] at this
  have hreal : ∀ k x, ((e k : K →+* ℂ) x).im = 0 := by
    intro k x
    show (e k x).im = 0
    have hx : x ∈ Algebra.adjoin ℚ {α} := htop ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx, he]; simp
    | algebraMap q => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | mul x y _ _ hx hy => simp [Complex.mul_im, hx, hy]
  refine ⟨fun k => toReal (e k : K →+* ℂ) (hreal k), ?_, ?_, ?_⟩
  · intro k
    apply Complex.ofReal_injective
    rw [toReal_coe]; exact he k
  · intro x
    apply Complex.ofReal_injective
    push_cast
    simp only [toReal_coe]
    have := trace_eq_sum_embeddings (K := ℚ) ℂ (x := x)
    rw [show ((Algebra.trace ℚ K x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ K x) by simp, this]
    exact (Equiv.sum_comp e (fun φ => φ x)).symm
  · intro x
    apply Complex.ofReal_injective
    push_cast
    simp only [toReal_coe]
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    rw [show ((Algebra.norm ℚ x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) by simp, this]
    exact (Equiv.prod_comp e (fun φ => φ x)).symm

end CCAux


namespace CCAux

lemma ex_up {s d L M Mu du Ll : ℝ} (h : s * d = L) (hs : s ^ 2 ≤ M) (hM : M ≤ Mu)
    (hd1 : -du ≤ d) (hd2 : d ≤ du) (hL : Ll ≤ |L|) (hLl : 0 ≤ Ll) (hc : Mu * du ^ 2 < Ll ^ 2) :
    False := by
  have hd : d ^ 2 ≤ du ^ 2 := by nlinarith
  have hL2 : Ll ^ 2 ≤ L ^ 2 := by
    have := sq_abs L
    nlinarith [abs_nonneg L]
  have hM0 : 0 ≤ M := le_trans (sq_nonneg s) hs
  have e : L ^ 2 = s ^ 2 * d ^ 2 := by rw [← h]; ring
  have : s ^ 2 * d ^ 2 ≤ M * du ^ 2 := mul_le_mul hs hd (sq_nonneg _) hM0
  nlinarith [sq_nonneg du]

lemma ex_lo {s d L M Mu dl Lu : ℝ} (h : s * d = L) (hs : 1 ≤ s ^ 2 * M) (hM : M ≤ Mu)
    (hM' : 0 ≤ M) (hd : dl ≤ |d|) (hdl : 0 ≤ dl) (hL1 : -Lu ≤ L) (hL2 : L ≤ Lu)
    (hc : Lu ^ 2 * Mu < dl ^ 2) : False := by
  have hd2 : dl ^ 2 ≤ d ^ 2 := by
    have := sq_abs d
    nlinarith [abs_nonneg d]
  have hLs : L ^ 2 ≤ Lu ^ 2 := by nlinarith
  have e : L ^ 2 = s ^ 2 * d ^ 2 := by rw [← h]; ring
  have h3 : d ^ 2 ≤ s ^ 2 * M * d ^ 2 := by nlinarith [sq_nonneg d]
  have h4 : s ^ 2 * M * d ^ 2 = L ^ 2 * M := by rw [e]; ring
  have h5 : L ^ 2 * M ≤ Lu ^ 2 * Mu := mul_le_mul hLs hM hM' (sq_nonneg _)
  linarith

lemma triv {s d L : ℝ} (h : s * d = L) (hL : L = d) (hd : d ≠ 0) : s = 1 := by
  rw [hL] at h
  exact mul_eq_right₀ hd |>.mp h

lemma trivn {s d L : ℝ} (h : s * d = L) (hL : L = -d) (hd : d ≠ 0) : s = -1 := by
  rw [hL, show -d = (-1) * d by ring] at h
  exact mul_right_cancel₀ hd h

lemma abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg a).trans ha)

lemma sq_bound {s M H : ℝ} (hs : s ^ 2 ≤ M) (hM : M ≤ H ^ 2) (hH : 0 ≤ H) : |s| ≤ H := by
  apply abs_le_of_sq_le_sq' (by linarith) hH |> fun h => abs_le.mpr h

set_option maxHeartbeats 4000000 in
lemma enum (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (h1 : (1.24697960 : ℝ) < r)
    (h2 : r < 1.24697961) (s0 s1 s2 M0 M1 M2 : ℝ)
    (hM0 : M0 ≤ 4.0490) (hM1 : M1 ≤ 2.2470) (hM2 : M2 ≤ 2.8020)
    (hM0' : 0 ≤ M0) (hM1' : 0 ≤ M1) (hM2' : 0 ≤ M2)
    (hb0 : s0 ^ 2 ≤ M0 ∧ 1 ≤ s0 ^ 2 * M0) (hb1 : s1 ^ 2 ≤ M1 ∧ 1 ≤ s1 ^ 2 * M1)
    (hb2 : s2 ^ 2 ≤ M2 ∧ 1 ≤ s2 ^ 2 * M2) (T0 T1 T2 : ℤ)
    (hT0 : (T0 : ℝ) = s0 + s1 + s2)
    (hT1 : (T1 : ℝ) = s0 * r + s1 * (r ^ 2 - 2) + s2 * (1 - r - r ^ 2))
    (hT2 : (T2 : ℝ) = s0 * r ^ 2 + s1 * (r ^ 2 - 2) ^ 2 + s2 * (1 - r - r ^ 2) ^ 2)
    (hN : s0 * s1 * s2 = 1 ∨ s0 * s1 * s2 = -1) :
    (s0 = 1 ∧ s1 = 1 ∧ s2 = 1) ∨ (s0 = -1 ∧ s1 = -1 ∧ s2 = -1) := by
  have hq1 : (1.24697960 : ℝ) ^ 2 < r ^ 2 := by nlinarith
  have hq2 : r ^ 2 < (1.24697961 : ℝ) ^ 2 := by nlinarith
  norm_num at hq1 hq2
  have hl0 : s0 * (3 + 4 * r - r ^ 2) = T0 + (r ^ 2 + r) * T1 + r * T2 := by
    linear_combination (-1) * hT0 + (-(r ^ 2 + r)) * hT1 + (-r) * hT2 +
      ((-1)*r^2*s1 + (-1)*r^2*s2 + (-2)*s0 + (1)*s1 + (1)*s2) * hr
  have hl1 : s1 * (5 * r ^ 2 + r - 8) = T0 + (1 - r) * T1 + (r ^ 2 - 2) * T2 := by
    linear_combination (-1) * hT0 + (-(1 - r)) * hT1 + (-(r ^ 2 - 2)) * hT2 +
      ((-1)*r^3*s1 + (-1)*r^3*s2 + (1)*r^2*s1 + (-1)*r^2*s2 + (-1)*r*s0 + (3)*r*s1 + (2)*r*s2 + (1)*s0 + (-1)*s1) * hr
  have hl2 : s2 * (5 - 5 * r - 4 * r ^ 2) = T0 + (3 - r ^ 2) * T1 + (1 - r - r ^ 2) * T2 := by
    linear_combination (-1) * hT0 + (-(3 - r ^ 2)) * hT1 + (-(1 - r - r ^ 2)) * hT2 +
      ((1)*r^3*s1 + (1)*r^3*s2 + (2)*r^2*s2 + (1)*r*s0 + (-2)*r*s1 + (-1)*r*s2 + (1)*s0 + (-1)*s1) * hr
  have hd0 : (3 + 4 * r - r ^ 2) ≠ 0 := by intro h; linarith
  have hd1 : (5 * r ^ 2 + r - 8) ≠ 0 := by intro h; linarith
  have hd2 : (5 - 5 * r - 4 * r ^ 2) ≠ 0 := by intro h; linarith
  -- integer bounds on the traces
  have a0 : |s0| ≤ 2.0123 := sq_bound hb0.1 (by linarith) (by norm_num)
  have a1 : |s1| ≤ 1.4991 := sq_bound hb1.1 (by linarith) (by norm_num)
  have a2 : |s2| ≤ 1.6740 := sq_bound hb2.1 (by linarith) (by norm_num)
  have p1 : |r| ≤ 1.24697961 := by rw [abs_le]; constructor <;> linarith
  have p2 : |r ^ 2 - 2| ≤ 0.4451 := by rw [abs_le]; constructor <;> linarith
  have p3 : |1 - r - r ^ 2| ≤ 1.8020 := by rw [abs_le]; constructor <;> linarith
  have p4 : |r ^ 2| ≤ 1.5550 := by rw [abs_le]; constructor <;> linarith
  have p5 : |(r ^ 2 - 2) ^ 2| ≤ 0.1982 := by
    rw [abs_pow]; nlinarith [abs_nonneg (r ^ 2 - 2)]
  have p6 : |(1 - r - r ^ 2) ^ 2| ≤ 3.2473 := by
    rw [abs_pow]; nlinarith [abs_nonneg (1 - r - r ^ 2)]
  have bT0 : |(T0 : ℝ)| ≤ 2.0123 + 1.4991 + 1.6740 := by
    rw [hT0]; exact (abs_add_le _ _).trans (by linarith [abs_add_le s0 s1])
  have bT1 : |(T1 : ℝ)| ≤ 2.0123 * 1.24697961 + 1.4991 * 0.4451 + 1.6740 * 1.8020 := by
    rw [hT1]
    have := abs_mul_le' a0 p1
    have := abs_mul_le' a1 p2
    have := abs_mul_le' a2 p3
    exact (abs_add_le _ _).trans (by linarith [abs_add_le (s0 * r) (s1 * (r ^ 2 - 2))])
  have bT2 : |(T2 : ℝ)| ≤ 2.0123 * 1.5550 + 1.4991 * 0.1982 + 1.6740 * 3.2473 := by
    rw [hT2]
    have := abs_mul_le' a0 p4
    have := abs_mul_le' a1 p5
    have := abs_mul_le' a2 p6
    exact (abs_add_le _ _).trans (by linarith [abs_add_le (s0 * r ^ 2) (s1 * (r ^ 2 - 2) ^ 2)])
  rw [abs_le] at bT0 bT1 bT2
  norm_num at bT0 bT1 bT2
  have iT0 : -5 ≤ T0 ∧ T0 ≤ 5 := by
    constructor
    · have : (-6 : ℝ) < T0 := by linarith
      have : (-6 : ℤ) < T0 := by exact_mod_cast this
      omega
    · have : (T0 : ℝ) < 6 := by linarith
      have : T0 < (6 : ℤ) := by exact_mod_cast this
      omega
  have iT1 : -6 ≤ T1 ∧ T1 ≤ 6 := by
    constructor
    · have : (-7 : ℝ) < T1 := by linarith
      have : (-7 : ℤ) < T1 := by exact_mod_cast this
      omega
    · have : (T1 : ℝ) < 7 := by linarith
      have : T1 < (7 : ℤ) := by exact_mod_cast this
      omega
  have iT2 : -8 ≤ T2 ∧ T2 ≤ 8 := by
    constructor
    · have : (-9 : ℝ) < T2 := by linarith
      have : (-9 : ℤ) < T2 := by exact_mod_cast this
      omega
    · have : (T2 : ℝ) < 9 := by linarith
      have : T2 < (9 : ℤ) := by exact_mod_cast this
      omega
  -- the norm equation
  have hP : (ccP T0 T1 T2 : ℝ) = -49 * (s0 * s1 * s2) := by
    have hprod : (s0 * (3 + 4 * r - r ^ 2)) * (s1 * (5 * r ^ 2 + r - 8)) *
        (s2 * (5 - 5 * r - 4 * r ^ 2)) = (T0 + (r ^ 2 + r) * T1 + r * T2) *
        (T0 + (1 - r) * T1 + (r ^ 2 - 2) * T2) * (T0 + (3 - r ^ 2) * T1 + (1 - r - r ^ 2) * T2) := by
      rw [hl0, hl1, hl2]
    unfold ccP
    push_cast
    set t0 : ℝ := (T0 : ℝ)
    set t1 : ℝ := (T1 : ℝ)
    set t2 : ℝ := (T2 : ℝ)
    linear_combination (-1) * hprod + (s0 * s1 * s2 * ((20)*r^3 + (-71)*r^2 + (-117)*r + (71)) -
      ((-1)*r^3*t1^2*t2 + (-1)*r^3*t1*t2^2 + (1)*r^2*t1^3 + (1)*r^2*t1^2*t2 + (-2)*r^2*t1*t2^2 + (-1)*r^2*t2^3 + (-1)*r*t0*t1^2 + (-1)*r*t0*t1*t2 + (-1)*r*t0*t2^2 + (-1)*r*t1^3 + (4)*r*t1^2*t2 + (3)*r*t1*t2^2 + (-1)*t1^3 + (-1)*t1^2*t2 + (2)*t1*t2^2 + (1)*t2^3)) * hr
  have hP' : ccP T0 T1 T2 = 49 ∨ ccP T0 T1 T2 = -49 := by
    rcases hN with h | h
    · right; rw [h] at hP; exact_mod_cast (by linarith : (ccP T0 T1 T2 : ℝ) = -49)
    · left; rw [h] at hP; exact_mod_cast (by linarith : (ccP T0 T1 T2 : ℝ) = 49)
  have hmem := ccDec T0 (Finset.mem_Icc.mpr iT0) T1 (Finset.mem_Icc.mpr iT1) T2
    (Finset.mem_Icc.mpr iT2) hP'
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals push_cast at hl0 hl1 hl2
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 1.4766) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl0 hb0.2 hM0 hM0' (dl := 6.4329) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 1.2742) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 1.0218) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 1.8412) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl0 hb0.2 hM0 hM0' (dl := 6.4329) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 0.5671) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_up hl0 hb0.1 hM0 (du := 6.4330) (by linarith) (by linarith) (Ll := 26.0465) (by rw [le_abs]; right; linarith) (by norm_num) (by norm_num)).elim
  · right; exact ⟨trivn hl0 (by ring) hd0, trivn hl1 (by ring) hd1, trivn hl2 (by ring) hd2⟩
  · exact (ex_up hl1 hb1.1 hM1 (du := 1.0218) (by linarith) (by linarith) (Ll := 4.1370) (by rw [le_abs]; right; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_lo hl1 hb1.2 hM1 hM1' (dl := 1.0217) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 0.5671) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_up hl2 hb2.1 hM2 (du := 7.4548) (by linarith) (by linarith) (Ll := 16.7506) (by rw [le_abs]; left; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_up hl1 hb1.1 hM1 (du := 1.0218) (by linarith) (by linarith) (Ll := 2.2958) (by rw [le_abs]; right; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 3.3177) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_up hl1 hb1.1 hM1 (du := 1.0218) (by linarith) (by linarith) (Ll := 1.8411) (by rw [le_abs]; right; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_lo hl1 hb1.2 hM1 hM1' (dl := 1.0217) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 0.4548) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 0.8194) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 0.8194) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl1 hb1.2 hM1 hM1' (dl := 1.0217) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 0.4548) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_up hl1 hb1.1 hM1 (du := 1.0218) (by linarith) (by linarith) (Ll := 1.8411) (by rw [le_abs]; left; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 3.3177) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_up hl1 hb1.1 hM1 (du := 1.0218) (by linarith) (by linarith) (Ll := 2.2958) (by rw [le_abs]; left; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_up hl2 hb2.1 hM2 (du := 7.4548) (by linarith) (by linarith) (Ll := 16.7506) (by rw [le_abs]; right; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_lo hl1 hb1.2 hM1 hM1' (dl := 1.0217) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 0.5671) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_up hl1 hb1.1 hM1 (du := 1.0218) (by linarith) (by linarith) (Ll := 4.1370) (by rw [le_abs]; left; linarith) (by norm_num) (by norm_num)).elim
  · left; exact ⟨triv hl0 (by ring) hd0, triv hl1 (by ring) hd1, triv hl2 (by ring) hd2⟩
  · exact (ex_up hl0 hb0.1 hM0 (du := 6.4330) (by linarith) (by linarith) (Ll := 26.0465) (by rw [le_abs]; left; linarith) (by norm_num) (by norm_num)).elim
  · exact (ex_lo hl0 hb0.2 hM0 hM0' (dl := 6.4329) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 0.5671) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 1.8412) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 1.0218) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl0 hb0.2 hM0 hM0' (dl := 6.4329) (by rw [le_abs]; left; linarith) (by norm_num) (Lu := 1.2742) (by linarith) (by linarith) (by norm_num)).elim
  · exact (ex_lo hl2 hb2.2 hM2 hM2' (dl := 7.4547) (by rw [le_abs]; right; linarith) (by norm_num) (Lu := 1.4766) (by linarith) (by linarith) (by norm_num)).elim

end CCAux


namespace CCAux

lemma sq_box {t M : ℝ} (ht : 0 < t) (hM : 0 < M) (h : |2 * Real.log t| ≤ Real.log M) :
    t ^ 2 ≤ M ∧ 1 ≤ t ^ 2 * M := by
  have ht2 : t ^ 2 = Real.exp (2 * Real.log t) := by
    rw [← Real.log_rpow ht, Real.exp_log (by positivity)]; norm_num
  rw [abs_le] at h
  constructor
  · rw [ht2, ← Real.exp_log hM]; exact Real.exp_le_exp.mpr h.2
  · rw [ht2, ← Real.exp_log hM, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)

lemma hb {u K : ℝ} (hu1 : -(1/2) ≤ u) (hu2 : u ≤ 1/2) (hK : 0 ≤ K) :
    -(K/2) ≤ u * K ∧ u * K ≤ K/2 := by constructor <;> nlinarith

lemma log3 {p x y : ℝ} (hp : 0 < p) (hx : 0 < x) (hy : 0 < y) (a b : ℤ) :
    Real.log (p * x ^ (-a) * y ^ (-b)) = Real.log p - a * Real.log x - b * Real.log y := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_zpow, Real.log_zpow]
  push_cast; ring

/-- reduction of a positive vector of norm one into the box of the lattice spanned by the
log vectors `(A,B,C)` and `(C,A,B)` -/
lemma real_box (r : ℝ) (hr : r ^ 3 + r ^ 2 - 2 * r - 1 = 0) (h1 : (1.24697960 : ℝ) < r)
    (h2 : r < 1.24697961) (p0 p1 p2 : ℝ) (hp0 : 0 < p0) (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hprod : p0 * p1 * p2 = 1) :
    ∃ a b : ℤ,
      (p0 * (r ^ 2 + r - 1) ^ (-a) * (2 - r ^ 2) ^ (-b)) ^ 2 ≤ (r ^ 2 + r - 1) / (2 - r ^ 2) ∧
      1 ≤ (p0 * (r ^ 2 + r - 1) ^ (-a) * (2 - r ^ 2) ^ (-b)) ^ 2 * ((r ^ 2 + r - 1) / (2 - r ^ 2)) ∧
      (p1 * r ^ (-a) * (r ^ 2 + r - 1) ^ (-b)) ^ 2 ≤ r * (r ^ 2 + r - 1) ∧
      1 ≤ (p1 * r ^ (-a) * (r ^ 2 + r - 1) ^ (-b)) ^ 2 * (r * (r ^ 2 + r - 1)) ∧
      (p2 * (2 - r ^ 2) ^ (-a) * r ^ (-b)) ^ 2 ≤ r / (2 - r ^ 2) ∧
      1 ≤ (p2 * (2 - r ^ 2) ^ (-a) * r ^ (-b)) ^ 2 * (r / (2 - r ^ 2)) := by
  have he : 1 < r ^ 2 + r - 1 := by nlinarith
  have hg0 : 0 < 2 - r ^ 2 := by nlinarith
  have hg1 : 2 - r ^ 2 < 1 := by nlinarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 < r := by linarith
  set e := r ^ 2 + r - 1 with he_def
  set g := 2 - r ^ 2 with hg_def
  have hegr : e * r * g = 1 := by rw [he_def, hg_def]; linear_combination (-r ^ 2 + 1) * hr
  set A := Real.log e
  set B := Real.log r
  set C := Real.log g
  have hA : 0 < A := Real.log_pos he
  have hB : 0 < B := Real.log_pos hr1
  have hC : C < 0 := Real.log_neg hg0 hg1
  have hABC : A + B + C = 0 := by
    have := congrArg Real.log hegr
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_one] at this
  set l0 := Real.log p0
  set l1 := Real.log p1
  set l2 := Real.log p2
  have hl : l0 + l1 + l2 = 0 := by
    have := congrArg Real.log hprod
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_one] at this
  set D := A ^ 2 - B * C
  have hD : 0 < D := by nlinarith
  set x := (l0 * A - l1 * C) / D
  set y := (A * l1 - B * l0) / D
  have ex0 : l0 = x * A + y * C := by
    simp only [x, y]; field_simp; ring
  have ex1 : l1 = x * B + y * A := by
    simp only [x, y]; field_simp; ring
  have ex2 : l2 = x * C + y * B := by
    have : C = -A - B := by linarith
    have : l2 = -l0 - l1 := by linarith
    rw [this, ex0, ex1]; rw [‹C = -A - B›]; ring
  refine ⟨round x, round y, ?_⟩
  have hx := abs_sub_round x
  have hy := abs_sub_round y
  rw [abs_le] at hx hy
  set u := x - round x
  set w := y - round y
  have b0 : |2 * Real.log (p0 * e ^ (-round x) * g ^ (-round y))| ≤ Real.log (e / g) := by
    rw [log3 hp0 (by positivity) hg0, Real.log_div (by positivity) hg0.ne', abs_le]
    have : l0 - (round x : ℝ) * A - (round y : ℝ) * C = u * A + w * C := by
      simp only [u, w]; rw [ex0]; ring
    rw [this]
    have := hb hx.1 hx.2 hA.le
    have := hb hy.1 hy.2 (neg_nonneg.mpr hC.le)
    constructor <;> linarith
  have b1 : |2 * Real.log (p1 * r ^ (-round x) * e ^ (-round y))| ≤ Real.log (r * e) := by
    rw [log3 hp1 hr0 (by positivity), Real.log_mul hr0.ne' (by positivity), abs_le]
    have : l1 - (round x : ℝ) * B - (round y : ℝ) * A = u * B + w * A := by
      simp only [u, w]; rw [ex1]; ring
    rw [this]
    have := hb hx.1 hx.2 hB.le
    have := hb hy.1 hy.2 hA.le
    constructor <;> linarith
  have b2 : |2 * Real.log (p2 * g ^ (-round x) * r ^ (-round y))| ≤ Real.log (r / g) := by
    rw [log3 hp2 hg0 hr0, Real.log_div hr0.ne' hg0.ne', abs_le]
    have : l2 - (round x : ℝ) * C - (round y : ℝ) * B = u * C + w * B := by
      simp only [u, w]; rw [ex2]; ring
    rw [this]
    have := hb hx.1 hx.2 (neg_nonneg.mpr hC.le)
    have := hb hy.1 hy.2 hB.le
    constructor <;> linarith
  obtain ⟨c0, c0'⟩ := sq_box (by positivity) (by positivity) b0
  obtain ⟨c1, c1'⟩ := sq_box (by positivity) (by positivity) b1
  obtain ⟨c2, c2'⟩ := sq_box (by positivity) (by positivity) b2
  exact ⟨c0, c0', c1, c1', c2, c2'⟩

end CCAux


set_option maxHeartbeats 4000000 in
theorem solution (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (α : K) (hα : α ^ 3 + α ^ 2 - 2 * α - 1 = 0) :
    (α ^ 2 + α - 1) ≠ 0 ∧ (2 - α ^ 2) ≠ 0 ∧
    (∀ u : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ a b : ℤ,
        ((u : 𝓞 K) : K) = ((ζ : 𝓞 K) : K) * (α ^ 2 + α - 1) ^ a * (2 - α ^ 2) ^ b) ∧
    (∀ a b : ℤ, (∃ n : ℕ, 0 < n ∧ ((α ^ 2 + α - 1) ^ a * (2 - α ^ 2) ^ b) ^ n = 1) →
        a = 0 ∧ b = 0) := by
  classical
  obtain ⟨r, hr, h1, h2⟩ := CCAux.exists_root
  obtain ⟨σ, hσα, htr, hnm⟩ := CCAux.setup r hr h1 h2 hK α hα
  have s0 : σ 0 α = r := by simpa [CCAux.ρ] using hσα 0
  have s1 : σ 1 α = r ^ 2 - 2 := by simpa [CCAux.ρ] using hσα 1
  have s2 : σ 2 α = 1 - r - r ^ 2 := by simpa [CCAux.ρ] using hσα 2
  have v10 : σ 0 (α ^ 2 + α - 1) = r ^ 2 + r - 1 := by
    simp only [map_sub, map_add, map_pow, map_one, s0]
  have v11 : σ 1 (α ^ 2 + α - 1) = -r := by
    simp only [map_sub, map_add, map_pow, map_one, s1]; linear_combination (r - 1) * hr
  have v12 : σ 2 (α ^ 2 + α - 1) = 2 - r ^ 2 := by
    simp only [map_sub, map_add, map_pow, map_one, s2]; linear_combination (r + 1) * hr
  have v20 : σ 0 (2 - α ^ 2) = 2 - r ^ 2 := by
    simp only [map_sub, map_pow, map_ofNat, s0]
  have v21 : σ 1 (2 - α ^ 2) = r ^ 2 + r - 1 := by
    simp only [map_sub, map_pow, map_ofNat, s1]; linear_combination (-r + 1) * hr
  have v22 : σ 2 (2 - α ^ 2) = -r := by
    simp only [map_sub, map_pow, map_ofNat, s2]; linear_combination (-r - 1) * hr
  have he : 1 < r ^ 2 + r - 1 := by nlinarith
  have hg0 : 0 < 2 - r ^ 2 := by nlinarith
  have hg1 : 2 - r ^ 2 < 1 := by nlinarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 < r := by linarith
  have hε1 : α ^ 2 + α - 1 ≠ 0 := by
    intro h; have := congrArg (σ 0) h; rw [v10, map_zero] at this; linarith
  have hε2 : 2 - α ^ 2 ≠ 0 := by
    intro h; have := congrArg (σ 0) h; rw [v20, map_zero] at this; linarith
  refine ⟨hε1, hε2, ?_, ?_⟩
  · intro u
    have hαint : IsIntegral ℤ α := by
      refine ⟨Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1, ?_, ?_⟩
      · monicity!
      · simp [hα]
    let a : 𝓞 K := ⟨α, hαint⟩
    have ha : ((a : 𝓞 K) : K) = α := rfl
    let U1 : (𝓞 K)ˣ := ⟨a ^ 2 + a - 1, a ^ 2 - 1,
      by apply RingOfIntegers.coe_injective; push_cast [ha]; linear_combination α * hα,
      by apply RingOfIntegers.coe_injective; push_cast [ha]; linear_combination α * hα⟩
    let U2 : (𝓞 K)ˣ := ⟨1 + 1 - a ^ 2, 1 + a,
      by apply RingOfIntegers.coe_injective; push_cast [ha]; linear_combination (-1) * hα,
      by apply RingOfIntegers.coe_injective; push_cast [ha]; linear_combination (-1) * hα⟩
    have hU1 : (U1 : K) = α ^ 2 + α - 1 := by
      show ((a ^ 2 + a - 1 : 𝓞 K) : K) = _; push_cast [ha]; rfl
    have hU2 : (U2 : K) = 2 - α ^ 2 := by
      show ((1 + 1 - a ^ 2 : 𝓞 K) : K) = _; push_cast [ha]; ring
    set x : K := (u : K) with hxdef
    have hx0 : x ≠ 0 := Units.coe_ne_zero u
    have hnorm1 : ∀ w : (𝓞 K)ˣ, |((Algebra.norm ℚ (w : K) : ℚ) : ℝ)| = 1 := by
      intro w; have := Units.norm K w; rw [← Rat.cast_abs, this, Rat.cast_one]
    have hprod : |σ 0 x| * |σ 1 x| * |σ 2 x| = 1 := by
      have := hnm x; rw [Fin.prod_univ_three] at this
      rw [← abs_mul, ← abs_mul, ← this]; exact hnorm1 u
    have hp : ∀ k, 0 < |σ k x| := fun k => abs_pos.mpr ((map_ne_zero (σ k)).mpr hx0)
    obtain ⟨a', b', c0, c0', c1, c1', c2, c2'⟩ :=
      CCAux.real_box r hr h1 h2 _ _ _ (hp 0) (hp 1) (hp 2) hprod
    set v := u * U1 ^ (-a') * U2 ^ (-b') with hvdef
    have hv : (v : K) = x * (α ^ 2 + α - 1) ^ (-a') * (2 - α ^ 2) ^ (-b') := by
      rw [hvdef, Units.coe_mul, Units.coe_mul, Units.coe_zpow, Units.coe_zpow, hU1, hU2]
    set y : K := (v : K) with hydef
    have sv0 : |σ 0 y| = |σ 0 x| * (r ^ 2 + r - 1) ^ (-a') * (2 - r ^ 2) ^ (-b') := by
      rw [hv, map_mul, map_mul, map_zpow₀, map_zpow₀, v10, v20, abs_mul, abs_mul, abs_zpow,
        abs_zpow, abs_of_pos (by linarith : (0:ℝ) < r ^ 2 + r - 1), abs_of_pos hg0]
    have sv1 : |σ 1 y| = |σ 1 x| * r ^ (-a') * (r ^ 2 + r - 1) ^ (-b') := by
      rw [hv, map_mul, map_mul, map_zpow₀, map_zpow₀, v11, v21, abs_mul, abs_mul, abs_zpow,
        abs_zpow, abs_neg, abs_of_pos hr0, abs_of_pos (by linarith : (0:ℝ) < r ^ 2 + r - 1)]
    have sv2 : |σ 2 y| = |σ 2 x| * (2 - r ^ 2) ^ (-a') * r ^ (-b') := by
      rw [hv, map_mul, map_mul, map_zpow₀, map_zpow₀, v12, v22, abs_mul, abs_mul, abs_zpow,
        abs_zpow, abs_neg, abs_of_pos hr0, abs_of_pos hg0]
    have hyint : ∀ j : ℕ, ∃ T : ℤ, (T : ℝ) = ∑ k, σ k (y * α ^ j) := by
      intro j
      have hi : IsIntegral ℤ (Algebra.trace ℚ K (y * α ^ j)) := by
        apply Algebra.isIntegral_trace
        have : y * α ^ j = (((v : 𝓞 K) * a ^ j : 𝓞 K) : K) := by
          push_cast [ha]; rfl
        rw [this]; exact RingOfIntegers.isIntegral_coe _
      obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
      exact ⟨n, by rw [← htr, ← hn]; simp⟩
    obtain ⟨T0, hT0⟩ := hyint 0
    obtain ⟨T1, hT1⟩ := hyint 1
    obtain ⟨T2, hT2⟩ := hyint 2
    simp only [Fin.sum_univ_three, map_mul, map_pow, s0, s1, s2, pow_zero, mul_one,
      pow_one] at hT0 hT1 hT2
    have hN : σ 0 y * σ 1 y * σ 2 y = 1 ∨ σ 0 y * σ 1 y * σ 2 y = -1 := by
      have := hnm y; rw [Fin.prod_univ_three] at this
      rw [← this]; exact abs_eq (zero_le_one) |>.mp (hnorm1 v)
    have hq2 : r ^ 2 < (1.24697961 : ℝ) ^ 2 := by nlinarith
    norm_num at hq2
    have hM0 : (r ^ 2 + r - 1) / (2 - r ^ 2) ≤ 4.0490 := by
      rw [div_le_iff₀ hg0]; linarith
    have hM1 : r * (r ^ 2 + r - 1) ≤ 2.2470 := by
      have : r * (r ^ 2 + r - 1) = r + 1 := by linear_combination hr
      rw [this]; linarith
    have hM2 : r / (2 - r ^ 2) ≤ 2.8020 := by rw [div_le_iff₀ hg0]; linarith
    rw [← sv0, sq_abs] at c0 c0'
    rw [← sv1, sq_abs] at c1 c1'
    rw [← sv2, sq_abs] at c2 c2'
    have hfin := CCAux.enum r hr h1 h2 (σ 0 y) (σ 1 y) (σ 2 y) _ _ _ hM0 hM1 hM2
      (by positivity) (by positivity) (by positivity) ⟨c0, c0'⟩ ⟨c1, c1'⟩ ⟨c2, c2'⟩ T0 T1 T2
      hT0 hT1 hT2 hN
    have hy2 : y ^ 2 = 1 := by
      apply (σ 0).injective
      rw [map_pow, map_one]
      rcases hfin with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h] <;> norm_num
    refine ⟨v, isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, ?_⟩, a', b', ?_⟩
    · apply Units.coe_injective K
      show ((v ^ 2 : (𝓞 K)ˣ) : K) = ((1 : (𝓞 K)ˣ) : K)
      rw [Units.coe_pow, Units.coe_one, ← hydef, hy2]
    · show x = y * _ * _
      rw [hv, zpow_neg, zpow_neg]
      have hP := zpow_ne_zero a' hε1
      have hQ := zpow_ne_zero b' hε2
      generalize (α ^ 2 + α - 1) ^ a' = P at hP ⊢
      generalize (2 - α ^ 2) ^ b' = Q at hQ ⊢
      field_simp
  · rintro a b ⟨n, hn, h⟩
    have hA := Real.log_pos he
    have hB := Real.log_pos hr1
    have hC := Real.log_neg hg0 hg1
    have hABC : Real.log (r ^ 2 + r - 1) + Real.log r + Real.log (2 - r ^ 2) = 0 := by
      rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul (by positivity) (by positivity)]
      rw [show (r ^ 2 + r - 1) * r * (2 - r ^ 2) = 1 by linear_combination (-r ^ 2 + 1) * hr]
      exact Real.log_one
    have e0 := congrArg (fun z => Real.log |σ 0 z|) h
    have e1 := congrArg (fun z => Real.log |σ 1 z|) h
    simp only [map_pow, map_mul, map_zpow₀, map_one, v10, v20, v11, v21, abs_pow, abs_mul,
      abs_zpow, abs_neg, abs_one, Real.log_one] at e0 e1
    rw [abs_of_pos (by linarith : (0:ℝ) < r ^ 2 + r - 1), abs_of_pos hg0] at e0
    rw [abs_of_pos hr0, abs_of_pos (by linarith : (0:ℝ) < r ^ 2 + r - 1)] at e1
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_zpow,
      Real.log_zpow] at e0 e1
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have f0 := (mul_eq_zero.mp e0).resolve_left hn'
    have f1 := (mul_eq_zero.mp e1).resolve_left hn'
    set A := Real.log (r ^ 2 + r - 1)
    set B := Real.log r
    set C := Real.log (2 - r ^ 2)
    have hD : 0 < A ^ 2 - B * C := by nlinarith
    have ha : (a : ℝ) = 0 := by
      have : (a : ℝ) * (A ^ 2 - B * C) = 0 := by linear_combination A * f0 - C * f1
      exact (mul_eq_zero.mp this).resolve_right hD.ne'
    have hb : (b : ℝ) = 0 := by
      rw [ha, zero_mul, zero_add] at f0
      exact (mul_eq_zero.mp f0).resolve_right hC.ne
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

