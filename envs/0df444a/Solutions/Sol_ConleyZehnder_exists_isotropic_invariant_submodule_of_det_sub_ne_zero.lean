-- Prove2me | solution 1 for ConleyZehnder.exists_isotropic_invariant_submodule_of_det_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:30:17.353292+00:00
-- url     : https://prove2.me/submissions/f25d6ee8-6415-4b0f-b879-718cedd60d9e

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_complexLinearDet_mul_four_pow
import Theorems.Thm_ConleyZehnder_argLift_square_increment
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Complex.Polynomial.Basic

open ConleyZehnder Matrix
open ConleyZehnder Matrix Module Polynomial

namespace CZ13

variable {n : ℕ}

/-- complexified matrix -/
noncomputable abbrev cx (M : Mat n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  M.map (fun x : ℝ => (x : ℂ))

lemma cx_eq (M : Mat n) : cx M = (Complex.ofRealHom).mapMatrix M := rfl

lemma cx_mul (M N : Mat n) : cx (M * N) = cx M * cx N := by
  simp only [cx_eq, map_mul]

lemma cx_one : cx (1 : Mat n) = 1 := by simp only [cx_eq, map_one]

lemma cx_det (M : Mat n) : (cx M).det = (M.det : ℂ) := by
  rw [cx_eq, ← RingHom.map_det]; rfl

/-- `det (a • 1 + b • M)` for the complexification of `M`. -/
noncomputable def Q (a b : ℂ) (M : Mat n) : ℂ := (a • (1 : Matrix _ _ ℂ) + b • cx M).det

noncomputable def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

lemma norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  rw [phase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 hz)]

lemma phase_eq_exp {z : ℂ} (hz : z ≠ 0) : phase z = Complex.exp (z.arg * Complex.I) := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [phase, div_eq_iff hn]
  exact h.symm.trans (mul_comm _ _)

lemma phase_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    phase (∏ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  simp only [phase, norm_prod, Complex.ofReal_prod, Finset.prod_div_distrib]

lemma phase_real_mul_sq {c : ℝ} (hc : c ≠ 0) (w : ℂ) : phase ((c : ℂ) * w) ^ 2 = phase w ^ 2 := by
  have hcc : ((|c| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hc
  have h2 : ((c : ℂ) / ((|c| : ℝ) : ℂ)) ^ 2 = 1 := by
    rw [div_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs, div_self]
    exact_mod_cast pow_ne_zero 2 hc
  simp only [phase, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul]
  rw [show (c : ℂ) * w / (((|c| : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ)) =
      ((c : ℂ) / ((|c| : ℝ) : ℂ)) * (w / ((‖w‖ : ℝ) : ℂ)) by
    rw [mul_div_mul_comm], mul_pow, h2, one_mul]

lemma phase_real_sq {c : ℝ} (hc : c ≠ 0) : phase (c : ℂ) ^ 2 = 1 := by
  have := phase_real_mul_sq hc 1
  rw [mul_one] at this
  rw [this]; simp [phase]

/-! ### Spectral decomposition of a real symmetric matrix -/

/-- the orthogonal eigenvector matrix -/
noncomputable def evU {N : Mat n} (hN : N.IsHermitian) : Mat n := (hN.eigenvectorUnitary : Mat n)

lemma evU_spec {N : Mat n} (hN : N.IsHermitian) :
    N = evU hN * diagonal hN.eigenvalues * (evU hN)ᵀ ∧ (evU hN)ᵀ * evU hN = 1 ∧
      evU hN * (evU hN)ᵀ = 1 := by
  have h1 := hN.spectral_theorem
  have hs : (star (hN.eigenvectorUnitary : Mat n)) = (evU hN)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]; rfl
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [h1]
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp, hs]
    rfl
  · rw [← hs]; exact Unitary.coe_star_mul_self _
  · rw [← hs]; exact Unitary.coe_mul_star_self _

lemma Q_conj {U : Mat n} (hU : U * Uᵀ = 1) (d : Fin n ⊕ Fin n → ℝ) (a b : ℂ) :
    Q a b (U * diagonal d * Uᵀ) = ∏ i, (a + b * d i) := by
  have hdiag : diagonal (fun i => a + b * d i) = a • (1 : Matrix _ _ ℂ) + b • cx (diagonal d) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [diagonal]
    · simp [diagonal, h, one_apply]
  have hUU : cx U * cx Uᵀ = 1 := by rw [← cx_mul, hU, cx_one]
  have key : a • (1 : Matrix _ _ ℂ) + b • cx (U * diagonal d * Uᵀ) =
      cx U * diagonal (fun i => a + b * d i) * cx Uᵀ := by
    rw [hdiag, cx_mul, cx_mul, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc,
      Matrix.mul_one, hUU, mul_smul_comm, smul_mul_assoc]
  unfold Q
  rw [key, det_mul, det_mul, det_diagonal]
  have : (cx U).det * (cx Uᵀ).det = 1 := by rw [← det_mul, hUU, det_one]
  linear_combination (∏ i, (a + b * d i)) * this

lemma Q_symm {N : Mat n} (hN : N.IsHermitian) (a b : ℂ) :
    Q a b N = ∏ i, (a + b * hN.eigenvalues i) := by
  obtain ⟨h1, -, h3⟩ := evU_spec hN
  conv_lhs => rw [h1]
  exact Q_conj h3 _ a b

lemma isHermitian_of_transpose {M : Mat n} (h : Mᵀ = M) : M.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, h]

lemma Q_ne_zero_one {N : Mat n} (hN : Nᵀ = N) (s : ℝ) : Q 1 (-Complex.I * s) N ≠ 0 := by
  rw [Q_symm (isHermitian_of_transpose hN)]
  rw [Finset.prod_ne_zero_iff]
  intro i _ h
  have := congrArg Complex.re h
  simp at this

lemma Q_ne_zero_I {N : Mat n} (hN : Nᵀ = N) (s : ℝ) : Q (-Complex.I) s N ≠ 0 := by
  rw [Q_symm (isHermitian_of_transpose hN)]
  rw [Finset.prod_ne_zero_iff]
  intro i _ h
  have := congrArg Complex.im h
  simp at this

lemma continuous_Q (a : ℂ) {b : unitInterval × unitInterval → ℂ} (hb : Continuous b)
    {M : unitInterval × unitInterval → Mat n} (hM : Continuous M) :
    Continuous fun p => Q a (b p) (M p) := by
  unfold Q cx
  exact (continuous_const.add (hb.smul (hM.matrix_map Complex.continuous_ofReal))).matrix_det

/-! ### Arguments of products -/

lemma isArgLift_phase_sq_prod {ι : Type*} [Fintype ι] (z : unitInterval → ι → ℂ)
    (hc : ∀ i, Continuous fun t => z t i) (hs : ∀ t i, z t i ∈ Complex.slitPlane) :
    IsArgLift (fun t => phase (∏ i, z t i) ^ 2) (fun t => ∑ i, 2 * (z t i).arg) := by
  refine ⟨continuous_finset_sum _ fun i _ => continuous_const.mul ?_, fun t => ?_⟩
  · exact continuous_iff_continuousAt.2 fun t =>
      ContinuousAt.comp (f := fun t => z t i) (Complex.continuousAt_arg (hs t i))
        (hc i).continuousAt
  · show phase (∏ i, z t i) ^ 2 = Complex.exp (((∑ i, 2 * (z t i).arg : ℝ) : ℂ) * Complex.I)
    rw [phase_prod, ← Finset.prod_pow]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [phase_eq_exp (Complex.slitPlane_ne_zero (hs t i)), sq, ← Complex.exp_add]
    ring_nf

lemma isArgLift_const (w : ℂ) (hw : ‖w‖ = 1) :
    IsArgLift (fun _ : unitInterval => w) (fun _ => w.arg) := by
  refine ⟨continuous_const, fun _ => ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw, Complex.ofReal_one, one_mul] at h
  exact h.symm

lemma isArgLift_sq {f : unitInterval → ℂ} {θ : unitInterval → ℝ} (h : IsArgLift f θ) :
    IsArgLift (fun t => f t ^ 2) (fun t => 2 * θ t) := by
  refine ⟨continuous_const.mul h.1, fun t => ?_⟩
  show f t ^ 2 = Complex.exp (((2 * θ t : ℝ) : ℂ) * Complex.I)
  rw [h.2 t, sq, ← Complex.exp_add]
  push_cast
  ring_nf

/-- increments of any two lifts of the same function agree -/
lemma incr_eq {f : unitInterval → ℂ} {θ θ' : unitInterval → ℝ} (h : IsArgLift f θ)
    (h' : IsArgLift f θ') : θ 1 - θ 0 = θ' 1 - θ' 0 := by
  have hf : Continuous f := by
    have : f = fun t => Complex.exp ((θ t : ℂ) * Complex.I) := funext h.2
    rw [this]; exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp h.1).mul continuous_const)
  have h1 : ∀ t, ‖f t‖ = 1 := fun t => by
    rw [h.2 t, Complex.norm_exp_ofReal_mul_I]
  exact (argLift_exists_increment_unique hf h1).2 θ θ' h h'

end CZ13

namespace CZ14

open CZ13

variable {n : ℕ}

abbrev Vec (n : ℕ) := Fin n ⊕ Fin n → ℂ

/-- the complexified matrix as an endomorphism -/
noncomputable def fA (A : Mat n) : Module.End ℂ (Vec n) := Matrix.toLin' (cx A)

/-- the complex bilinear symplectic pairing `ω(v, w) = v ⬝ J₀ w` -/
noncomputable def ω (n : ℕ) : LinearMap.BilinForm ℂ (Vec n) := Matrix.toBilin' (cx (J₀ n))

lemma ω_apply (v w : Vec n) : ω n v w = v ⬝ᵥ (cx (J₀ n) *ᵥ w) := Matrix.toBilin'_apply' _ _ _

lemma fA_apply (A : Mat n) (v : Vec n) : fA A v = cx A *ᵥ v := Matrix.toLin'_apply _ _

lemma cx_transpose (M : Mat n) : cx Mᵀ = (cx M)ᵀ := by ext i j; rfl

lemma ω_fA {A : Mat n} (hs : IsSymplectic A) (v w : Vec n) :
    ω n (fA A v) (fA A w) = ω n v w := by
  have hJ : Aᵀ * J₀ n * A = J₀ n := (SymplecticGroup.mem_iff').1 hs
  have hc : (cx A)ᵀ * cx (J₀ n) * cx A = cx (J₀ n) := by
    rw [← cx_transpose, ← cx_mul, ← cx_mul, hJ]
  rw [ω_apply, ω_apply, fA_apply, fA_apply, mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, dotProduct_mulVec, ← Matrix.mul_assoc, hc]

/-- `ω (v, (1 - μ f)^j x) = ω ((f - μ)^j v, f^j x)` -/
lemma ω_shift {A : Mat n} (hs : IsSymplectic A) (μ : ℂ) (j : ℕ) (v x : Vec n) :
    ω n v (aeval (fA A) ((1 - C μ * X) ^ j) x) =
      ω n (((fA A - μ • 1) ^ j) v) (((fA A) ^ j) x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have hcomm : aeval (fA A) ((1 - C μ * X) ^ (j + 1)) =
        aeval (fA A) ((1 - C μ * X) ^ j) * (1 - μ • fA A) := by
      rw [pow_succ, map_mul]
      congr 1
      simp [Algebra.smul_def]
    rw [hcomm, Module.End.mul_apply, ih]
    set u := ((fA A - μ • 1) ^ j) v
    have hpc : ((fA A) ^ j) ((1 - μ • fA A) x) = (1 - μ • fA A) (((fA A) ^ j) x) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      congr 1
      exact ((Commute.one_right _).sub_right ((Commute.refl _).smul_right μ)).pow_left j |>.eq
    rw [hpc, pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    set z := ((fA A) ^ j) x
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply]
    rw [← ω_fA hs u z]

lemma coprime_lin {μ ν : ℂ} (h : μ * ν ≠ 1) : IsCoprime (X - C ν) (1 - C μ * X) := by
  have h1 : (1 - μ * ν) ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  refine ⟨C (μ / (1 - μ * ν)), C (1 / (1 - μ * ν)), ?_⟩
  have e : μ / (1 - μ * ν) * ν = 1 / (1 - μ * ν) - 1 := by field_simp; ring
  have e2 : 1 / (1 - μ * ν) * μ = μ / (1 - μ * ν) := by ring
  calc C (μ / (1 - μ * ν)) * (X - C ν) + C (1 / (1 - μ * ν)) * (1 - C μ * X)
      = C (μ / (1 - μ * ν)) * X - C (μ / (1 - μ * ν) * ν) + C (1 / (1 - μ * ν)) -
          C (1 / (1 - μ * ν) * μ) * X := by simp only [map_mul]; ring
    _ = 1 := by rw [e, e2, map_sub, map_one]; ring

/-- generalized eigenvectors for eigenvalues with `μ ν ≠ 1` are `ω`-orthogonal -/
lemma ω_gen_eq_zero {A : Mat n} (hs : IsSymplectic A) {μ ν : ℂ} (h : μ * ν ≠ 1) {v w : Vec n}
    (hv : v ∈ (fA A).maxGenEigenspace μ) (hw : w ∈ (fA A).maxGenEigenspace ν) :
    ω n v w = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
  obtain ⟨a, b, hab⟩ := ((coprime_lin h).pow (m := m) (n := k))
  have hP : aeval (fA A) ((X - C ν) ^ m) = (fA A - ν • 1) ^ m := by
    simp [Algebra.smul_def]
  have hw' : w = aeval (fA A) ((1 - C μ * X) ^ k) (aeval (fA A) b w) := by
    have := congrArg (fun p => aeval (fA A) p w) hab
    simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply, hP, hm, map_zero, zero_add] at this
    calc w = aeval (fA A) b (aeval (fA A) ((1 - C μ * X) ^ k) w) := this.symm
      _ = _ := by
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  rw [hw', ω_shift hs, hk]
  simp

/-- generalized eigenvalue subspaces for a set of eigenvalues -/
noncomputable def genSum (A : Mat n) (P : ℂ → Prop) : Submodule ℂ (Vec n) :=
  ⨆ (μ : ℂ) (_ : P μ), (fA A).maxGenEigenspace μ

lemma genSum_isotropic {A : Mat n} (hs : IsSymplectic A) {P : ℂ → Prop}
    (hP : ∀ μ ν, P μ → P ν → μ * ν ≠ 1) :
    ∀ v ∈ genSum A P, ∀ w ∈ genSum A P, ω n v w = 0 := by
  intro v hv w hw
  have h1 : genSum A P ≤ LinearMap.ker ((ω n).flip w) := by
    refine iSup₂_le fun μ hμ x hx => ?_
    have h2 : genSum A P ≤ LinearMap.ker (ω n x) := by
      refine iSup₂_le fun ν hν y hy => ?_
      rw [LinearMap.mem_ker]
      exact ω_gen_eq_zero hs (hP μ ν hμ hν) hx hy
    rw [LinearMap.mem_ker]
    exact LinearMap.mem_ker.1 (h2 hw)
  exact LinearMap.mem_ker.1 (h1 hv)

lemma gen_eq_bot {A : Mat n} {μ : ℂ}
    (hdet : (A.map (fun x : ℝ => (x : ℂ)) - μ • 1).det ≠ 0) :
    (fA A).maxGenEigenspace μ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  have he : fA A - μ • (1 : Module.End ℂ (Vec n)) = Matrix.toLin' (cx A - μ • 1) := by
    rw [map_sub, map_smul, Matrix.toLin'_one]; rfl
  have hinj : Function.Injective ⇑(fA A - μ • (1 : Module.End ℂ (Vec n))) := by
    rw [he]
    exact (Matrix.mulVec_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)))
  have hinjk : Function.Injective ⇑((fA A - μ • (1 : Module.End ℂ (Vec n))) ^ k) := by
    rw [Module.End.coe_pow]; exact hinj.iterate k
  rw [Submodule.mem_bot]
  exact hinjk (by rw [hk, map_zero])

lemma genSum_sup_eq_top {A : Mat n}
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    genSum A (fun μ => ‖μ‖ < 1) ⊔ genSum A (fun μ => 1 < ‖μ‖) = ⊤ := by
  rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top (fA A)]
  refine iSup_le fun μ => ?_
  rcases lt_trichotomy ‖μ‖ 1 with h | h | h
  · exact le_sup_of_le_left (le_iSup₂_of_le μ h le_rfl)
  · rw [gen_eq_bot (hcirc μ h)]; exact bot_le
  · exact le_sup_of_le_right (le_iSup₂_of_le μ h le_rfl)

lemma ω_ker_eq_bot : LinearMap.ker (ω n) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have h1 : v ᵥ* cx (J₀ n) = 0 := by
    funext j
    have := LinearMap.congr_fun hv (Pi.single j 1)
    rw [ω_apply, dotProduct_mulVec, LinearMap.zero_apply] at this
    simpa using this
  have hJu : IsUnit (cx (J₀ n)) := by
    rw [isUnit_iff_isUnit_det, cx_det]
    exact isUnit_iff_ne_zero.2 (by
      have := congrArg det (J_squared (Fin n) ℝ)
      intro h0
      rw [det_mul, show (J₀ n).det = 0 by exact_mod_cast h0, zero_mul, det_neg, det_one] at this
      simp at this)
  rw [Submodule.mem_bot]
  exact (Matrix.vecMul_injective_iff_isUnit.2 hJu)
    (show v ᵥ* cx (J₀ n) = 0 ᵥ* cx (J₀ n) by rw [h1, zero_vecMul])

lemma finrank_le_of_isotropic {W : Submodule ℂ (Vec n)} (hW : ∀ v ∈ W, ∀ w ∈ W, ω n v w = 0) :
    finrank ℂ W ≤ n := by
  have h := (ω n).finrank_add_finrank_orthogonal' W
  have hle : W ≤ (ω n).orthogonal W := fun w hw v hv => hW v hv w hw
  have h2 := Submodule.finrank_mono hle
  have hk : (W ⊓ LinearMap.ker (ω n) : Submodule ℂ (Vec n)) = ⊥ := by
    rw [ω_ker_eq_bot, inf_bot_eq]
  rw [show (ω n).ker = LinearMap.ker (ω n) from rfl, hk, finrank_bot,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- a hyperbolic symplectic matrix has an `n`-dimensional invariant, conjugation-stable,
`ω`-isotropic complex subspace -/
theorem exists_isotropic {A : Mat n} (hs : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    ∃ L : Submodule ℂ (Vec n), n ≤ finrank ℂ L ∧ (∀ v ∈ L, cx A *ᵥ v ∈ L) ∧
      (∀ v ∈ L, star v ∈ L) ∧ ∀ v ∈ L, ∀ w ∈ L, ω n v w = 0 := by
  set L := genSum A (fun μ => ‖μ‖ < 1)
  set U := genSum A (fun μ => 1 < ‖μ‖)
  have hL : ∀ v ∈ L, ∀ w ∈ L, ω n v w = 0 := genSum_isotropic hs fun μ ν hμ hν h => by
    have : ‖μ * ν‖ < 1 := by
      rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hμ hν.le
    rw [h, norm_one] at this; exact lt_irrefl _ this
  have hU : ∀ v ∈ U, ∀ w ∈ U, ω n v w = 0 := genSum_isotropic hs fun μ ν hμ hν h => by
    have : 1 < ‖μ * ν‖ := by
      rw [norm_mul]; exact one_lt_mul_of_lt_of_le hμ hν.le
    rw [h, norm_one] at this; exact lt_irrefl _ this
  have hdimL := finrank_le_of_isotropic hL
  have hdimU := finrank_le_of_isotropic hU
  have htop := genSum_sup_eq_top hcirc
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq L U
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin] at hsum
  refine ⟨L, by omega, ?_, ?_, hL⟩
  · -- invariance
    have : L ≤ L.comap (fA A) := by
      refine iSup₂_le fun μ hμ v hv => ?_
      rw [Submodule.mem_comap]
      refine le_iSup₂_of_le (f := fun μ (_ : ‖μ‖ < 1) => (fA A).maxGenEigenspace μ) μ hμ le_rfl ?_
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
      refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
      rw [← Module.End.mul_apply, ← ((Commute.refl (fA A)).sub_right
        ((Commute.one_right _).smul_right μ)).pow_right k |>.eq, Module.End.mul_apply, hk, map_zero]
    intro v hv
    have := this hv
    rwa [Submodule.mem_comap, fA_apply] at this
  · -- conjugation
    have hstar : ∀ v : Vec n, fA A (star v) = star (fA A v) := fun v => by
      rw [fA_apply, fA_apply, star_mulVec, ← vecMul_transpose]
      congr 1
      ext i j
      simp [conjTranspose_apply]
    let L' : Submodule ℂ (Vec n) :=
      { carrier := {v | star v ∈ L}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, star_add] at *; exact L.add_mem ha hb
        zero_mem' := by simp
        smul_mem' := fun c v hv => by
          simp only [Set.mem_setOf_eq, star_smul] at *; exact L.smul_mem _ hv }
    have : L ≤ L' := by
      refine iSup₂_le fun μ hμ v hv => ?_
      show star v ∈ L
      refine le_iSup₂_of_le (f := fun μ (_ : ‖μ‖ < 1) => (fA A).maxGenEigenspace μ)
        (star μ) (by rwa [norm_star]) le_rfl ?_
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
      refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
      have key : ∀ j (x : Vec n), ((fA A - star μ • (1 : Module.End ℂ (Vec n))) ^ j) (star x) =
          star (((fA A - μ • (1 : Module.End ℂ (Vec n))) ^ j) x) := by
        intro j
        induction j with
        | zero => intro x; simp
        | succ j ih =>
          intro x
          have h1 : (fA A - star μ • (1 : Module.End ℂ (Vec n))) (star x) =
              star ((fA A - μ • (1 : Module.End ℂ (Vec n))) x) := by
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hstar,
              star_sub, star_smul]
          rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h1, ih]
      rw [key, hk, star_zero]
    exact fun v hv => this hv

end CZ14

open ConleyZehnder

open Matrix Module

theorem solution {n : ℕ} {A : Mat n}
    (hs : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    ∃ L : Submodule ℂ (Fin n ⊕ Fin n → ℂ), n ≤ finrank ℂ L ∧
      (∀ v ∈ L, A.map (fun x : ℝ => (x : ℂ)) *ᵥ v ∈ L) ∧ (∀ v ∈ L, star v ∈ L) ∧
      ∀ v ∈ L, ∀ w ∈ L, v ⬝ᵥ ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ w) = 0 :=
  by
    obtain ⟨L, h1, h2, h3, h4⟩ := CZ14.exists_isotropic hs hcirc
    exact ⟨L, h1, h2, h3, fun v hv w hw => (CZ14.ω_apply v w).symm.trans (h4 v hv w hw)⟩
