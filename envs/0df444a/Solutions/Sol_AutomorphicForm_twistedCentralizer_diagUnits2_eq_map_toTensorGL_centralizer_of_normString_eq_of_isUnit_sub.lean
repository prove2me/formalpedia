-- Prove2me | solution 1 for AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f6d1868a-6287-5bbc-a568-7db75621aee4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions

noncomputable section

namespace TwCE

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)

section HNorm

variable (A : Type) [CommRing A] [Algebra K A]

theorem norm_algEquiv {S T : Type} [Ring S] [Ring T] [Algebra A S] [Algebra A T] (e : S ≃ₐ[A] T) (x : S) :
    Algebra.norm A (e x) = Algebra.norm A x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : (Algebra.lmul A T (e x) : T →ₗ[A] T) =
      (e.toLinearEquiv : S →ₗ[A] T) ∘ₗ (Algebra.lmul A S x : S →ₗ[A] S) ∘ₗ (e.toLinearEquiv.symm : T →ₗ[A] S) := by
    ext y
    simp [Algebra.coe_lmul_eq_mul]
  rw [h, LinearMap.det_conj]

theorem rcomm_tmul (a : A) (l : L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (a ⊗ₜ[K] l) = l ⊗ₜ[K] a := by
  rfl

theorem rcomm_map (g : L ≃ₐ[K] L) (z : A ⊗[K] L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) z) =
      AutomorphicForm.sigmaTensor K L A g (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [Algebra.TensorProduct.map_tmul, rcomm_tmul, rcomm_tmul]
    show (g : L →ₐ[K] L) l ⊗ₜ[K] (AlgHom.id K A) a = (Algebra.TensorProduct.map (g : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
    rw [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algebraMap_norm_eq_prod_sigmaTensor (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = ∏ g : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A g x := by
  classical
  set c := TensorProduct.RightActions.Algebra.TensorProduct.comm K A L with hc
  obtain ⟨z, rfl⟩ : ∃ z, x = c z := ⟨c.symm x, (c.apply_symm_apply x).symm⟩
  rw [norm_algEquiv, ← c.commutes, Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A z, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [hc, rcomm_map]

theorem sigmaTensor_iterate (i : ℕ) (x : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[i] x = AutomorphicForm.sigmaTensor K L A (σ ^ i) x := by
  induction i generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show l ⊗ₜ[K] a = (Algebra.TensorProduct.map ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A))
          ((Algebra.TensorProduct.map ((σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)) =
        (Algebra.TensorProduct.map ((σ * σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]

theorem list_prod_range_eq {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]

theorem orderOf_eq_finrank' (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank, orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]

theorem algebraMap_norm_eq_prod_range (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) =
      ((List.range (Module.finrank K L)).map fun i => (AutomorphicForm.sigmaTensor K L A σ)^[i] x).prod := by
  classical
  rw [algebraMap_norm_eq_prod_sigmaTensor, list_prod_range_eq]
  have hn : orderOf σ = Module.finrank K L := orderOf_eq_finrank' K L σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range (Module.finrank K L) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio, ← hn] at hi hj
    exact pow_injOn_Iio_orderOf hi hj hij
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  rw [← himg, Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sigmaTensor_iterate]

end HNorm

section HNorm2

variable (A : Type) [CommRing A] [Algebra K A]

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (diagUnits2 x y) =
      diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) x)
        (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

omit σ in
theorem diagUnits2_mul (x y x' y' : (L ⊗[K] A)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] A)ˣ) :
    (AutomorphicForm.sigmaGL K L A σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x)
        ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (diagUnits2 x y) =
      diagUnits2 (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x).prod)
        (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y).prod) := by
  unfold AutomorphicForm.normString
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul]

omit σ in
theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    AutomorphicForm.toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) a)
        (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]

omit σ in
theorem val_list_prod_iterate_map (f : L ⊗[K] A →* L ⊗[K] A) (x : (L ⊗[K] A)ˣ) (m : ℕ) :
    ((((List.range m).map fun i => (Units.map f)^[i] x).prod : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ((List.range m).map fun i => (⇑f)^[i] (x : L ⊗[K] A)).prod := by
  have hit : ∀ i, (((Units.map f)^[i] x : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑f)^[i] (x : L ⊗[K] A) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ih]
  induction m with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, Units.val_mul, ih, hit]

omit σ in
theorem algebraMap_tensor_injective : Function.Injective (algebraMap A (L ⊗[K] A)) := by
  have h : (algebraMap A (L ⊗[K] A) : A → L ⊗[K] A) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    funext a
    rw [TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]
  rw [h]
  exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

theorem norm_eq_of_normString_diagUnits2 (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Aˣ) (α β : (L ⊗[K] A)ˣ)
    (h : AutomorphicForm.normString K L A σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    Algebra.norm A (α : L ⊗[K] A) = a ∧ Algebra.norm A (β : L ⊗[K] A) = b := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at h
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at h00 h11
  rw [val_list_prod_iterate_map, Units.coe_map] at h00 h11
  have h00' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (α : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) a := h00
  have h11' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (β : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) b := h11
  rw [← algebraMap_norm_eq_prod_range K L σ A hgen] at h00' h11'
  exact ⟨algebraMap_tensor_injective K L A h00', algebraMap_tensor_injective K L A h11'⟩

end HNorm2

end TwCE

end

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A]
    (x y : Aˣ) (hxy : IsUnit ((x : A) - (y : A)))
    (d₁ d₂ : (L ⊗[K] A)ˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 d₁ d₂) = AutomorphicForm.toTensorGL K L A (diagUnits2 x y)) :
    AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 d₁ d₂) =
      (Subgroup.centralizer ({diagUnits2 x y} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) := by
  classical

  obtain ⟨hNx, hNy⟩ := TwCE.norm_eq_of_normString_diagUnits2 K L σ A hgen x y d₁ d₂ hN
  have hunit : IsUnit (Algebra.norm A ((diagUnits2 d₁ d₂ : GL (Fin 2) (L ⊗[K] A)) 0 0 : L ⊗[K] A) -
      Algebra.norm A ((diagUnits2 d₁ d₂ : GL (Fin 2) (L ⊗[K] A)) 1 1 : L ⊗[K] A)) := by
    simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    rw [hNx, hNy]; exact hxy
  have key := fun t => AutomorphicForm.mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm K L σ hgen A
    (diagUnits2 d₁ d₂) (by simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]) (by simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]) hunit t

  have hcent : ∀ t₀ : GL (Fin 2) A, t₀ ∈ Subgroup.centralizer ({diagUnits2 x y} : Set (GL (Fin 2) A)) ↔
      (t₀ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (t₀ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
    intro t₀
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' := congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A)) h
      simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at h'
      have e10 := congrFun (congrFun h' 1) 0
      have e01 := congrFun (congrFun h' 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at e10 e01

      obtain ⟨u, hu⟩ := hxy
      constructor
      · have : ((x : A) - (y : A)) * (t₀ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by rw [sub_mul]; linear_combination (-1 : A) * e10
        rw [← hu] at this
        exact (Units.mul_right_eq_zero u).mp this
      · have : ((x : A) - (y : A)) * (t₀ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by rw [sub_mul]; linear_combination e01
        rw [← hu] at this
        exact (Units.mul_right_eq_zero u).mp this
    · rintro ⟨h10, h01⟩
      apply Units.ext
      simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, mul_comm]

  have htt : ∀ (t₀ : GL (Fin 2) A) (i j : Fin 2),
      ((AutomorphicForm.toTensorGL K L A t₀ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((t₀ : Matrix (Fin 2) (Fin 2) A) i j) := by
    intro t₀ i j; rfl
  ext t
  rw [key, Subgroup.mem_map]
  constructor
  · rintro ⟨h10, h01, ⟨a, ha⟩, ⟨b, hb⟩⟩

    have hdet : IsUnit ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 * (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
      have : Matrix.det (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
          (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 * (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 := by
        rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
      rw [← this]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit t)
    have hua' : IsUnit ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) := isUnit_of_mul_isUnit_left hdet
    have hub' : IsUnit ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := isUnit_of_mul_isUnit_right hdet
    have hincl : ∀ c : A, IsUnit ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) c) → IsUnit c := by
      intro c hc
      rcases subsingleton_or_nontrivial A with hA | hA
      · exact isUnit_of_subsingleton c
      haveI := hA
      have h1 := hc.map (Algebra.norm A)
      have h2 : (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) c = algebraMap A (L ⊗[K] A) c := by
        rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.RightActions.algebraMap_eval]
      rw [h2, Algebra.norm_algebraMap, TensorProduct.finrank_rightAlgebra] at h1
      exact (isUnit_pow_iff (Module.finrank_pos (R := K) (M := L)).ne').mp h1
    have hua : IsUnit a := hincl a (by rw [ha]; exact hua')
    have hub : IsUnit b := hincl b (by rw [hb]; exact hub')
    refine ⟨diagUnits2 hua.unit hub.unit, (hcent _).mpr ⟨by simp [LanglandsTunnell.CubicInduction.coe_diagUnits2],
      by simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]⟩, ?_⟩
    apply Units.ext
    ext i j
    rw [htt]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
        Matrix.head_fin_const, map_zero, IsUnit.unit_spec] <;>
      first | exact ha | exact hb | exact h01.symm | exact h10.symm
  · rintro ⟨t₀, ht₀, rfl⟩
    obtain ⟨h10, h01⟩ := (hcent t₀).mp ht₀
    refine ⟨by rw [htt, h10, map_zero], by rw [htt, h01, map_zero], ⟨_, (htt t₀ 0 0).symm⟩, ⟨_, (htt t₀ 1 1).symm⟩⟩

end S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
end P2MW
export P2MW.S_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub (solution)
