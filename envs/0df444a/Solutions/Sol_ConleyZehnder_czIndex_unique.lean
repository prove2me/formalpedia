-- Prove2me | solution 1 for ConleyZehnder.czIndex_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T11:29:28.804897+00:00
-- url     : https://prove2.me/submissions/2f95e05f-1a8e-4941-a4da-b79da9dc6014

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.SpecialFunctions.Exponential
import Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W
import Theorems.Thm_ConleyZehnder_czIndex_homotopy
import Theorems.Thm_ConleyZehnder_czIndex_loop
import Theorems.Thm_ConleyZehnder_czIndex_signature

open ConleyZehnder Matrix

namespace CZ19

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

variable {n : ℕ}

/-- Block matrix attached to `x = (z, u, v)`: on the pairs `j` with `b j` it is `diag(u, v)`,
on the other pairs it is the rotation-scaling `[[re z, -im z], [im z, re z]]`. -/
def blk (b : Fin n → Bool) (x : ℂ × ℝ × ℝ) : Mat n :=
  fromBlocks (diagonal fun j => if b j then x.2.1 else x.1.re)
    (diagonal fun j => if b j then 0 else -x.1.im)
    (diagonal fun j => if b j then 0 else x.1.im)
    (diagonal fun j => if b j then x.2.2 else x.1.re)

theorem blk_one (b : Fin n → Bool) : blk b 1 = 1 := by
  rw [← fromBlocks_one]
  unfold blk
  congr 1 <;> simp

theorem blk_zero (b : Fin n → Bool) : blk b 0 = 0 := by
  rw [← fromBlocks_zero]
  unfold blk
  congr 1 <;> simp

theorem blk_add (b : Fin n → Bool) (x y : ℂ × ℝ × ℝ) : blk b (x + y) = blk b x + blk b y := by
  unfold blk
  rw [fromBlocks_add]
  simp only [diagonal_add]
  congr 1 <;> (congr 1; funext j; cases b j <;> simp; try ring)

theorem blk_mul (b : Fin n → Bool) (x y : ℂ × ℝ × ℝ) : blk b (x * y) = blk b x * blk b y := by
  unfold blk
  rw [fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> (congr 1; funext j; cases b j <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

theorem blk_smul (b : Fin n → Bool) (t : ℝ) (x : ℂ × ℝ × ℝ) : blk b (t • x) = t • blk b x := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [blk, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.smul_apply, diagonal_apply, smul_eq_mul] <;>
    split_ifs <;> simp_all

/-- `blk b` as a ring homomorphism. -/
def blkHom (b : Fin n → Bool) : ℂ × ℝ × ℝ →+* Mat n where
  toFun := blk b
  map_one' := blk_one b
  map_mul' := blk_mul b
  map_zero' := blk_zero b
  map_add' := blk_add b

theorem blk_continuous (b : Fin n → Bool) : Continuous (blk b) := by
  unfold blk
  refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;>
  · refine Continuous.matrix_diagonal (continuous_pi fun j => ?_)
    cases b j <;> simp <;> fun_prop

theorem exp_blk (b : Fin n → Bool) (x : ℂ × ℝ × ℝ) :
    NormedSpace.exp (blk b x) = blk b (NormedSpace.exp x) :=
  (NormedSpace.map_exp (blkHom b) (blk_continuous b) x).symm

/-- The generator of the model path. -/
def genOf (a : ℝ) : ℂ × ℝ × ℝ := ((Real.pi : ℂ) * Complex.I, a, -a)

theorem exp_smul_genOf (t a : ℝ) :
    NormedSpace.exp (t • genOf a) =
      (Complex.exp ((t * Real.pi : ℝ) * Complex.I), Real.exp (t * a), Real.exp (-(t * a))) := by
  have h1 : (NormedSpace.exp (t • genOf a)).1 = Complex.exp ((t * Real.pi : ℝ) * Complex.I) := by
    rw [Prod.fst_exp, ← Complex.exp_eq_exp_ℂ]
    simp [genOf, Complex.real_smul]; ring_nf
  have h2 : (NormedSpace.exp (t • genOf a)).2.1 = Real.exp (t * a) := by
    rw [Prod.snd_exp, Prod.fst_exp, ← Real.exp_eq_exp_ℝ]
    simp [genOf]
  have h3 : (NormedSpace.exp (t • genOf a)).2.2 = Real.exp (-(t * a)) := by
    rw [Prod.snd_exp, Prod.snd_exp, ← Real.exp_eq_exp_ℝ]
    simp [genOf]
  ext <;> simp only [h1, h2, h3]

/-- The symmetric matrix `S` of the model path. -/
def Sm (b : Fin n → Bool) (a : ℝ) : Mat n :=
  fromBlocks (diagonal fun j => if b j then 0 else Real.pi)
    (diagonal fun j => if b j then -a else 0)
    (diagonal fun j => if b j then -a else 0)
    (diagonal fun j => if b j then 0 else Real.pi)

theorem J_mul_Sm (b : Fin n → Bool) (a : ℝ) : J₀ n * Sm b a = blk b (genOf a) := by
  unfold Sm blk genOf
  rw [show J₀ n = fromBlocks 0 (-1) 1 0 from rfl, fromBlocks_multiply]
  simp only [zero_mul, zero_add, add_zero, one_mul, neg_mul]
  congr 1 <;> (ext i k; by_cases h : i = k <;> simp [diagonal_apply, h] <;> cases b k <;> simp)

theorem Sm_isHermitian (b : Fin n → Bool) (a : ℝ) : (Sm b a).IsHermitian := by
  unfold IsHermitian Sm
  rw [conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose]
  simp

theorem Sm_mul_self (b : Fin n → Bool) (a : ℝ) :
    Sm b a * Sm b a =
      diagonal (Sum.elim (fun j => if b j then a ^ 2 else Real.pi ^ 2)
        (fun j => if b j then a ^ 2 else Real.pi ^ 2)) := by
  unfold Sm
  rw [fromBlocks_multiply, ← fromBlocks_diagonal]
  simp only [diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> (try ext i j) <;> (try (congr 1; funext j)) <;>
    simp [diagonal_apply] <;> (try split_ifs) <;> (try cases b j) <;> simp <;> ring

theorem Sm_det_ne_zero (b : Fin n → Bool) {a : ℝ} (ha : a ≠ 0) : (Sm b a).det ≠ 0 := by
  intro h
  have h2 := congrArg det (Sm_mul_self b a)
  rw [det_mul, h, mul_zero, det_diagonal] at h2
  refine (Finset.prod_ne_zero_iff.mpr fun k _ => ?_) h2.symm
  rcases k with k | k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> cases b k <;>
    simp [ha, Real.pi_ne_zero]

theorem Sm_eigenvalues_lt (b : Fin n → Bool) {a : ℝ} (ha : |a| < 2 * Real.pi)
    (i : Fin n ⊕ Fin n) : |(Sm_isHermitian b a).eigenvalues i| < 2 * Real.pi := by
  set hS := Sm_isHermitian b a
  set l := hS.eigenvalues i
  have hv := hS.mulVec_eigenvectorBasis i
  set v := hS.eigenvectorBasis i
  have h2 : (Sm b a * Sm b a) *ᵥ ⇑v = (l ^ 2) • ⇑v := by
    rw [← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul, sq]
  rw [Sm_mul_self] at h2
  have hne : v ≠ 0 := hS.eigenvectorBasis.orthonormal.ne_zero i
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (by ext k; simpa using hall k)
  have hk2 := congrFun h2 k
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hk2
  have hd := mul_right_cancel₀ hk hk2
  have hl : l ^ 2 < (2 * Real.pi) ^ 2 := by
    have hpi := Real.pi_pos
    have ha2 : a ^ 2 < (2 * Real.pi) ^ 2 := by
      have := abs_nonneg a
      nlinarith [sq_abs a]
    rw [← hd]
    rcases k with k | k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> nlinarith
  have hpi := Real.pi_pos
  exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

theorem blk_symplectic (b : Fin n → Bool) {x : ℂ × ℝ × ℝ} (h1 : x.1.re ^ 2 + x.1.im ^ 2 = 1)
    (h2 : x.2.1 * x.2.2 = 1) : IsSymplectic (blk b x) := by
  unfold IsSymplectic
  rw [SymplecticGroup.mem_iff, show Matrix.J (Fin n) ℝ = fromBlocks 0 (-1) 1 0 from rfl]
  unfold blk
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_transpose, zero_mul, mul_zero, zero_add, add_zero, mul_one, mul_neg, neg_mul,
    diagonal_mul_diagonal, ← diagonal_neg, diagonal_add]
  congr 1 <;> (ext i k; by_cases h : i = k <;> simp [diagonal_apply, one_apply, h] <;> cases b k <;> simp <;> nlinarith)

theorem blk_exp_symplectic (b : Fin n → Bool) (t a : ℝ) :
    IsSymplectic (blk b (NormedSpace.exp (t • genOf a))) := by
  rw [exp_smul_genOf]
  apply blk_symplectic
  · simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    exact Real.cos_sq_add_sin_sq _
  · simp only
    rw [← Real.exp_add]; simp

theorem blk_exp_neg_mul (b : Fin n → Bool) (x : ℂ × ℝ × ℝ) :
    blk b (NormedSpace.exp (-x)) * blk b (NormedSpace.exp x) = 1 := by
  rw [← blk_mul, ← NormedSpace.exp_add_of_commute (Commute.all _ _), neg_add_cancel,
    NormedSpace.exp_zero, blk_one]

theorem blk_exp_mul_neg (b : Fin n → Bool) (x : ℂ × ℝ × ℝ) :
    blk b (NormedSpace.exp x) * blk b (NormedSpace.exp (-x)) = 1 := by
  rw [← blk_mul, ← NormedSpace.exp_add_of_commute (Commute.all _ _), add_neg_cancel,
    NormedSpace.exp_zero, blk_one]

/-- The model path `t ↦ exp(t J₀ S)`. -/
def modelPath (b : Fin n → Bool) (a : ℝ) : C(unitInterval, Mat n) :=
  ⟨fun t => blk b (NormedSpace.exp ((t : ℝ) • genOf a)),
    (blk_continuous b).comp (NormedSpace.exp_continuous.comp
      (continuous_subtype_val.smul continuous_const))⟩

theorem modelPath_apply (b : Fin n → Bool) (a : ℝ) (t : unitInterval) :
    modelPath b a t = NormedSpace.exp ((t : ℝ) • (J₀ n * Sm b a)) := by
  rw [J_mul_Sm, ← blk_smul, exp_blk]
  rfl

theorem blk_endpoint (b : Fin n → Bool) :
    blk b (NormedSpace.exp ((1 : ℝ) • genOf (Real.log 2))) =
      blk b (-1, 2, 1 / 2) := by
  rw [exp_smul_genOf]
  congr 1
  simp only [one_mul, Complex.ofReal_one]
  rw [show ((Real.pi : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I from rfl, Complex.exp_pi_mul_I,
    Real.exp_neg, Real.exp_log (by norm_num)]
  simp

theorem blk_Wplus : blk (fun _ : Fin n => false) (-1, 2, 1 / 2) = Wplus n := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, Wplus, diagonal_apply, one_apply] <;> split_ifs <;> simp_all

theorem blk_Wminus : blk (fun j : Fin n => decide (j.val = 0)) (-1, 2, 1 / 2) = Wminus n := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, Wminus, diagonal_apply] <;> split_ifs <;> simp_all

end

end CZ19

namespace CZ19

noncomputable section

variable {n : ℕ}

/-- The family `(s, t) ↦ χ(s t) B ψ(t)`. -/
def famMap (ψ χ : C(unitInterval, Mat n)) (B : Mat n) : C(unitInterval × unitInterval, Mat n) :=
  ⟨fun p => χ ⟨(p.1 : ℝ) * p.2, unitInterval.mul_mem p.1.2 p.2.2⟩ * B * ψ p.2, by
    refine Continuous.matrix_mul (Continuous.matrix_mul (χ.continuous.comp ?_) continuous_const)
      (ψ.continuous.comp continuous_snd)
    exact Continuous.subtype_mk (by fun_prop) _⟩

/-- The correcting loop `t ↦ χ(t) B ψ(t) exp(-t J₀ S)`. -/
def loopOf (ψ χ : C(unitInterval, Mat n)) (B : Mat n) (b : Fin n → Bool) (a : ℝ) :
    C(unitInterval, Mat n) :=
  ⟨fun t => χ t * B * ψ t * blk b (NormedSpace.exp (-((t : ℝ) • genOf a))), by
    refine Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_mul χ.continuous
      continuous_const) ψ.continuous) ?_
    exact (blk_continuous b).comp (NormedSpace.exp_continuous.comp
      ((continuous_subtype_val.smul continuous_const).neg))⟩

theorem isSymplectic_mul {A B : Mat n} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) :=
  Submonoid.mul_mem _ hA hB

theorem key (μ : C(unitInterval, Mat n) → ℤ) (hH : HomotopyAxiom μ) (hL : LoopAxiom μ)
    (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) (χ : C(unitInterval, Mat n))
    (hχ0 : χ 0 = ψ 1) (hχ : ∀ t, χ t ∈ SpStar n) (b : Fin n → Bool) (a : ℝ)
    (hχ1 : χ 1 = blk b (NormedSpace.exp ((1 : ℝ) • genOf a))) (B : Mat n)
    (hB1 : ψ 1 * B = 1) (hB2 : B * ψ 1 = 1) (hBs : IsSymplectic B) :
    μ ψ = μ (modelPath b a) + 2 * maslovIndex (loopOf ψ χ B b a) := by
  set F := famMap ψ χ B
  have hF0 : F.curry 0 = ψ := by
    ext t : 1
    show χ ⟨((0 : unitInterval) : ℝ) * t, _⟩ * B * ψ t = ψ t
    have : (⟨((0 : unitInterval) : ℝ) * t, unitInterval.mul_mem (0 : unitInterval).2 t.2⟩ :
      unitInterval) = 0 := Subtype.ext (by simp)
    rw [this, hχ0, hB1, one_mul]
  have hF1 : ∀ t, F.curry 1 t = χ t * B * ψ t := by
    intro t
    show χ ⟨((1 : unitInterval) : ℝ) * t, _⟩ * B * ψ t = _
    have : (⟨((1 : unitInterval) : ℝ) * t, unitInterval.mul_mem (1 : unitInterval).2 t.2⟩ :
      unitInterval) = t := Subtype.ext (by simp)
    rw [this]
  have hFSP : ∀ s, F.curry s ∈ SP n := by
    intro s
    have hs1 : (⟨(s : ℝ) * ((1 : unitInterval) : ℝ), unitInterval.mul_mem s.2 (1 : unitInterval).2⟩ :
      unitInterval) = s := Subtype.ext (by simp)
    have hs0 : (⟨(s : ℝ) * ((0 : unitInterval) : ℝ), unitInterval.mul_mem s.2 (0 : unitInterval).2⟩ :
      unitInterval) = 0 := Subtype.ext (by simp)
    refine ⟨fun t => ?_, ?_, ?_⟩
    · exact isSymplectic_mul (isSymplectic_mul (hχ _).1 hBs) (hψ.1 t)
    · show χ ⟨(s : ℝ) * ((0 : unitInterval) : ℝ), _⟩ * B * ψ 0 = 1
      rw [hs0, hχ0, hψ.2.1, mul_one, hB1]
    · show (1 - χ ⟨(s : ℝ) * ((1 : unitInterval) : ℝ), _⟩ * B * ψ 1).det ≠ 0
      rw [hs1, mul_assoc, hB2, mul_one]
      exact (hχ s).2
  have hcomp : F.curry 1 ∈ connectedComponentIn (SP n) ψ :=
    (isPreconnected_range F.curry.continuous).subset_connectedComponentIn ⟨0, hF0⟩
      (Set.range_subset_iff.2 hFSP) ⟨1, rfl⟩
  have h1 := hH ψ hψ _ hcomp
  have hsym : ∀ t : ℝ, IsSymplectic (blk b (NormedSpace.exp (-(t • genOf a)))) := by
    intro t
    rw [← neg_smul]
    exact blk_exp_symplectic b (-t) a
  have hloop : IsSymplecticLoop (loopOf ψ χ B b a) := by
    refine ⟨fun t => ?_, ?_, ?_⟩
    · exact isSymplectic_mul (isSymplectic_mul (isSymplectic_mul (hχ _).1 hBs) (hψ.1 t)) (hsym t)
    · show χ 0 * B * ψ 0 * blk b (NormedSpace.exp (-(((0 : unitInterval) : ℝ) • genOf a))) = 1
      rw [hχ0, hB1, hψ.2.1, Set.Icc.coe_zero, zero_smul, neg_zero, NormedSpace.exp_zero, blk_one]
      simp
    · show χ 1 * B * ψ 1 * blk b (NormedSpace.exp (-(((1 : unitInterval) : ℝ) • genOf a))) = 1
      rw [mul_assoc (χ 1) B (ψ 1), hB2, mul_one, hχ1, Set.Icc.coe_one, blk_exp_mul_neg]
  have hmodel : modelPath b a ∈ SP n := by
    refine ⟨fun t => blk_exp_symplectic b t a, ?_, ?_⟩
    · show blk b (NormedSpace.exp (((0 : unitInterval) : ℝ) • genOf a)) = 1
      rw [Set.Icc.coe_zero, zero_smul, NormedSpace.exp_zero, blk_one]
    · show (1 - blk b (NormedSpace.exp (((1 : unitInterval) : ℝ) • genOf a))).det ≠ 0
      rw [Set.Icc.coe_one, ← hχ1]
      exact (hχ 1).2
  have hprod : loopOf ψ χ B b a * modelPath b a = F.curry 1 := by
    ext t : 1
    rw [hF1, ContinuousMap.mul_apply]
    show χ t * B * ψ t * blk b (NormedSpace.exp (-((t : ℝ) • genOf a))) *
      blk b (NormedSpace.exp ((t : ℝ) • genOf a)) = _
    rw [mul_assoc, blk_exp_neg_mul, mul_one]
  have h2 := hL _ hloop _ hmodel
  rw [hprod] at h2
  omega

theorem czIndex_unique' {n : ℕ} (μ : C(unitInterval, Mat n) → ℤ) (hH : HomotopyAxiom μ)
    (hL : LoopAxiom μ) (hS : SignatureAxiom μ) (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    μ ψ = czIndex ψ := by
  obtain ⟨χ, hχ0, hχ, hχ1⟩ := spStar_exists_path_to_W (ψ 1) ⟨hψ.1 1, hψ.2.2⟩
  set g : symplecticGroup (Fin n) ℝ := ⟨ψ 1, hψ.1 1⟩
  have hB1 : ψ 1 * ((g⁻¹ : symplecticGroup (Fin n) ℝ) : Mat n) = 1 := by
    exact congrArg Subtype.val (mul_inv_cancel g)
  have hB2 : ((g⁻¹ : symplecticGroup (Fin n) ℝ) : Mat n) * ψ 1 = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel g)
  have hBs : IsSymplectic ((g⁻¹ : symplecticGroup (Fin n) ℝ) : Mat n) := (g⁻¹).2
  set a := Real.log 2
  have ha : a ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have ha' : |a| < 2 * Real.pi := by
    rw [abs_of_pos (Real.log_pos (by norm_num))]
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    have := Real.two_le_pi
    linarith
  obtain ⟨b, hb⟩ : ∃ b : Fin n → Bool,
      χ 1 = blk b (NormedSpace.exp ((1 : ℝ) • genOf a)) := by
    rcases hχ1 with h | h
    · exact ⟨fun _ => false, by rw [h, blk_endpoint, blk_Wplus]⟩
    · exact ⟨fun j => decide (j.val = 0), by rw [h, blk_endpoint, blk_Wminus]⟩
  have kμ := key μ hH hL ψ hψ χ hχ0 hχ b a hb _ hB1 hB2 hBs
  have kc := key czIndex (czIndex_homotopy n) (czIndex_loop n) ψ hψ χ hχ0 hχ b a hb _ hB1 hB2 hBs
  have sμ := hS (Sm b a) (Sm_isHermitian b a) (Sm_det_ne_zero b ha) (Sm_eigenvalues_lt b ha')
    (modelPath b a) (modelPath_apply b a)
  have sc := czIndex_signature n (Sm b a) (Sm_isHermitian b a) (Sm_det_ne_zero b ha)
    (Sm_eigenvalues_lt b ha') (modelPath b a) (modelPath_apply b a)
  omega

end

end CZ19

open ConleyZehnder

theorem solution {n : ℕ} (μ : C(unitInterval, Mat n) → ℤ) (hH : HomotopyAxiom μ)
    (hL : LoopAxiom μ) (hS : SignatureAxiom μ) (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    μ ψ = czIndex ψ :=
  CZ19.czIndex_unique' μ hH hL hS ψ hψ
