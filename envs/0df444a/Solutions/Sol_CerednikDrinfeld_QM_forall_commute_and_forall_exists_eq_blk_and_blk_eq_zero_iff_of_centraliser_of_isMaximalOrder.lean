-- Prove2me | solution 1 for CerednikDrinfeld.QM.forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a010d3d7-fd96-56d8-8c3b-0134d3e3b555

import Mathlib
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
import Theorems.Thm_Matrix_exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

namespace CentModN

open Matrix

variable {N : ℕ} [NeZero N]

section Morita

variable {V : Type} [AddCommGroup V] [Module (ZMod N) V]
  (α : (Matrix (Fin 2) (Fin 2) (ZMod N)) →+* Module.End (ZMod N) V) (v₀ : V) (hv₀ : ∀ w : V, ∃! a : (Matrix (Fin 2) (Fin 2) (ZMod N)), w = α a v₀)

theorem α_smul (r : (ZMod N)) (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : α (r • a) = r • α a := by
  rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

def eps : (Matrix (Fin 2) (Fin 2) (ZMod N)) →ₗ[(ZMod N)] V where
  toFun a := α a v₀
  map_add' a b := by simp [map_add]
  map_smul' r a := by rw [α_smul]; rfl

@[scoped simp] theorem eps_apply (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : eps α v₀ a = α a v₀ := rfl

include hv₀ in
theorem eps_bijective : Function.Bijective (eps α v₀) := by
  refine ⟨fun a b h => ?_, fun w => ?_⟩
  · obtain ⟨c, hc, huniq⟩ := hv₀ (α a v₀)
    exact (huniq a rfl).trans (huniq b (show α a v₀ = α b v₀ from h)).symm
  · obtain ⟨a, ha, -⟩ := hv₀ w
    exact ⟨a, ha.symm⟩

noncomputable def epsE : (Matrix (Fin 2) (Fin 2) (ZMod N)) ≃ₗ[(ZMod N)] V := LinearEquiv.ofBijective (eps α v₀) (eps_bijective α v₀ hv₀)

@[scoped simp] theorem epsE_apply (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : epsE α v₀ hv₀ a = α a v₀ := rfl

theorem epsE_mul (b a : (Matrix (Fin 2) (Fin 2) (ZMod N))) : epsE α v₀ hv₀ (b * a) = α b (epsE α v₀ hv₀ a) := by
  simp [map_mul]

theorem epsE_one : epsE α v₀ hv₀ 1 = v₀ := by simp

noncomputable def cOf (β : Module.End (ZMod N) V) : (Matrix (Fin 2) (Fin 2) (ZMod N)) := (epsE α v₀ hv₀).symm (β v₀)

theorem epsE_cOf (β : Module.End (ZMod N) V) : epsE α v₀ hv₀ (cOf α v₀ hv₀ β) = β v₀ := by
  simp [cOf]

theorem comm_apply_epsE (β : Module.End (ZMod N) V) (hβ : β ∈ Subalgebra.centralizer (ZMod N) (Set.range α)) (a : (Matrix (Fin 2) (Fin 2) (ZMod N))) :
    β (epsE α v₀ hv₀ a) = epsE α v₀ hv₀ (a * cOf α v₀ hv₀ β) := by
  have hcomm : α a * β = β * α a := (Subalgebra.mem_centralizer_iff (ZMod N)).mp hβ _ ⟨a, rfl⟩
  rw [epsE_mul, epsE_cOf, epsE_apply, ← epsE_one α v₀ hv₀]
  show (β * α a) (epsE α v₀ hv₀ 1) = (α a * β) (epsE α v₀ hv₀ 1)
  rw [hcomm]

theorem cOf_mul (β₁ β₂ : Module.End (ZMod N) V) (h₁ : β₁ ∈ Subalgebra.centralizer (ZMod N) (Set.range α))
    (h₂ : β₂ ∈ Subalgebra.centralizer (ZMod N) (Set.range α)) :
    cOf α v₀ hv₀ (β₁ * β₂) = cOf α v₀ hv₀ β₂ * cOf α v₀ hv₀ β₁ := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, Module.End.mul_apply, ← epsE_cOf α v₀ hv₀ β₂, comm_apply_epsE α v₀ hv₀ β₁ h₁]

theorem cOf_one : cOf α v₀ hv₀ 1 = 1 := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, epsE_one]; rfl

theorem cOf_add (β₁ β₂ : Module.End (ZMod N) V) :
    cOf α v₀ hv₀ (β₁ + β₂) = cOf α v₀ hv₀ β₁ + cOf α v₀ hv₀ β₂ := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, map_add, epsE_cOf, epsE_cOf]; rfl

theorem cOf_smul (r : (ZMod N)) (β : Module.End (ZMod N) V) :
    cOf α v₀ hv₀ (r • β) = r • cOf α v₀ hv₀ β := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf, map_smul, epsE_cOf]; rfl

noncomputable def βOf (c : (Matrix (Fin 2) (Fin 2) (ZMod N))) : Module.End (ZMod N) V :=
  (epsE α v₀ hv₀).toLinearMap ∘ₗ (LinearMap.mulRight (ZMod N) c) ∘ₗ (epsE α v₀ hv₀).symm.toLinearMap

theorem βOf_mem (c : (Matrix (Fin 2) (Fin 2) (ZMod N))) : βOf α v₀ hv₀ c ∈ Subalgebra.centralizer (ZMod N) (Set.range α) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  apply LinearMap.ext; intro w
  obtain ⟨a, rfl⟩ := (epsE α v₀ hv₀).surjective w
  show α b (βOf α v₀ hv₀ c (epsE α v₀ hv₀ a)) = βOf α v₀ hv₀ c (α b (epsE α v₀ hv₀ a))
  simp only [βOf, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    LinearMap.mulRight_apply, ← epsE_mul, LinearEquiv.symm_apply_apply, mul_assoc]

theorem cOf_βOf (c : (Matrix (Fin 2) (Fin 2) (ZMod N))) : cOf α v₀ hv₀ (βOf α v₀ hv₀ c) = c := by
  apply (epsE α v₀ hv₀).injective
  rw [epsE_cOf]
  have h1 : (epsE α v₀ hv₀).symm v₀ = 1 := by rw [LinearEquiv.symm_apply_eq, epsE_one]
  show epsE α v₀ hv₀ (LinearMap.mulRight (ZMod N) c ((epsE α v₀ hv₀).symm v₀)) = epsE α v₀ hv₀ c
  rw [h1, LinearMap.mulRight_apply, one_mul]

theorem cOf_injective (β₁ β₂ : Module.End (ZMod N) V) (h₁ : β₁ ∈ Subalgebra.centralizer (ZMod N) (Set.range α))
    (h₂ : β₂ ∈ Subalgebra.centralizer (ZMod N) (Set.range α)) (h : cOf α v₀ hv₀ β₁ = cOf α v₀ hv₀ β₂) :
    β₁ = β₂ := by
  apply LinearMap.ext; intro w
  obtain ⟨a, rfl⟩ := (epsE α v₀ hv₀).surjective w
  rw [comm_apply_epsE α v₀ hv₀ β₁ h₁, comm_apply_epsE α v₀ hv₀ β₂ h₂, h]

end Morita

section MoritaCount

variable {V : Type} [AddCommGroup V] [Module (ZMod N) V]
  (α : (Matrix (Fin 2) (Fin 2) (ZMod N)) →+* Module.End (ZMod N) V) (v₀ : V) (hv₀ : ∀ w : V, ∃! a : (Matrix (Fin 2) (Fin 2) (ZMod N)), w = α a v₀)

include v₀ hv₀ in

theorem card_centralizer :
    Nat.card ↥(Subalgebra.centralizer (ZMod N) (Set.range α)) = N ^ 4 := by
  classical
  have hbij : Function.Bijective (fun β : ↥(Subalgebra.centralizer (ZMod N) (Set.range α)) => cOf α v₀ hv₀ β.1) := by
    constructor
    · intro β₁ β₂ h; exact Subtype.ext (cOf_injective α v₀ hv₀ _ _ β₁.2 β₂.2 h)
    · intro c; exact ⟨⟨βOf α v₀ hv₀ c, βOf_mem α v₀ hv₀ c⟩, cOf_βOf α v₀ hv₀ c⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  show Fintype.card (Fin 2 → Fin 2 → ZMod N) = N ^ 4
  rw [Fintype.card_pi, Fin.prod_univ_two, Fintype.card_pi, Fin.prod_univ_two, ZMod.card]; ring

end MoritaCount

end CentModN
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

namespace CentModN

open Matrix

variable {N : ℕ} [NeZero N]

section Blk

open scoped Quaternion
open QuaternionAlgebra

variable {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
  (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
  (hμ_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, μ ⟨1, h⟩ = 1)
  (hμ_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O), μ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = μ x * μ y)
  (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)

open Classical in

noncomputable def μ' (h : ℍ[ℚ, c, d]) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  if hh : h ∈ O then μ ⟨h, hh⟩ else 0

theorem μ'_of_mem (h : ℍ[ℚ, c, d]) (hh : h ∈ O) : μ' O μ h = μ ⟨h, hh⟩ := by
  simp [μ', hh]

include hμ_add in
theorem μ_zero : μ ⟨0, O.zero_mem⟩ = 0 := by
  have := hμ_add ⟨0, O.zero_mem⟩ ⟨0, O.zero_mem⟩
  have h2 : (⟨0, O.zero_mem⟩ : ↥O) + ⟨0, O.zero_mem⟩ = ⟨0, O.zero_mem⟩ := by simp
  rw [h2] at this
  have := congrArg (fun m => m - μ ⟨0, O.zero_mem⟩) this
  simpa using this.symm

end Blk
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

end CentModN
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

namespace CentModN

open Matrix

variable {N : ℕ} [NeZero N]

section Blk2

open scoped Quaternion
open QuaternionAlgebra

variable {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
  (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
  (hμ_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, μ ⟨1, h⟩ = 1)
  (hμ_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O), μ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = μ x * μ y)
  (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)

include hμ_add in
theorem μ'_zero : μ' O μ 0 = 0 := by
  rw [μ'_of_mem O μ 0 O.zero_mem]; exact μ_zero O μ hμ_add

include hμ_add in
theorem μ'_add (h₁ h₂ : ℍ[ℚ, c, d]) (hh₁ : h₁ ∈ O) (hh₂ : h₂ ∈ O) :
    μ' O μ (h₁ + h₂) = μ' O μ h₁ + μ' O μ h₂ := by
  rw [μ'_of_mem O μ _ (O.add_mem hh₁ hh₂), μ'_of_mem O μ _ hh₁, μ'_of_mem O μ _ hh₂, ← hμ_add]; rfl

include hμ_add in
theorem μ'_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℚ, c, d]) (hf : ∀ i ∈ s, f i ∈ O) :
    μ' O μ (∑ i ∈ s, f i) = ∑ i ∈ s, μ' O μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [μ'_zero O μ hμ_add]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      μ'_add O μ hμ_add _ _ (hf a (Finset.mem_insert_self a s))
        (O.sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

include hO hμ_mul in
theorem μ'_mul (h₁ h₂ : ℍ[ℚ, c, d]) (hh₁ : h₁ ∈ O) (hh₂ : h₂ ∈ O) :
    μ' O μ (h₁ * h₂) = μ' O μ h₁ * μ' O μ h₂ := by
  rw [μ'_of_mem O μ _ (hO.mul_mem hh₁ hh₂), μ'_of_mem O μ _ hh₁, μ'_of_mem O μ _ hh₂]
  exact hμ_mul ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩ _

include hO hμ_one in
theorem μ'_one : μ' O μ 1 = 1 := by
  rw [μ'_of_mem O μ _ hO.one_mem]; exact hμ_one _

noncomputable def blk (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N) where
  toFun w := fun i => ∑ l, μ' O μ (y i l) *ᵥ w l
  map_add' w w' := by
    funext i; simp only [Pi.add_apply, Matrix.mulVec_add, Finset.sum_add_distrib]
  map_smul' r w := by
    funext i; simp only [Pi.smul_apply, Matrix.mulVec_smul, Finset.smul_sum, RingHom.id_apply]

theorem blk_apply (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (w : Fin 2 → Fin 2 → ZMod N) :
    blk O μ y w = fun i => ∑ l, μ' O μ (y i l) *ᵥ w l := rfl

theorem blk_eq (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (w : Fin 2 → Fin 2 → ZMod N) :
    (fun i => ∑ l, μ ⟨y i l, hy i l⟩ *ᵥ w l) = blk O μ y w := by
  ext i j; simp [blk_apply, μ'_of_mem O μ _ (hy _ _)]

include hO hμ_mul hμ_add in
theorem blk_mul (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O) :
    blk O μ (y * y') = blk O μ y * blk O μ y' := by
  apply LinearMap.ext; intro w; funext i
  rw [Module.End.mul_apply, blk_apply, blk_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, blk_apply]
  rw [μ'_add O μ hμ_add _ _ (hO.mul_mem (hy _ _) (hy' _ _)) (hO.mul_mem (hy _ _) (hy' _ _)),
    μ'_add O μ hμ_add _ _ (hO.mul_mem (hy _ _) (hy' _ _)) (hO.mul_mem (hy _ _) (hy' _ _)),
    μ'_mul O hO μ hμ_mul _ _ (hy _ _) (hy' _ _), μ'_mul O hO μ hμ_mul _ _ (hy _ _) (hy' _ _),
    μ'_mul O hO μ hμ_mul _ _ (hy _ _) (hy' _ _), μ'_mul O hO μ hμ_mul _ _ (hy _ _) (hy' _ _)]
  simp only [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

include hO hμ_one hμ_add in
theorem blk_one : blk O μ 1 = 1 := by
  apply LinearMap.ext; intro w; funext i
  rw [blk_apply]
  simp only [Fin.sum_univ_two, Module.End.one_apply]
  fin_cases i <;> simp [Matrix.one_apply, μ'_one O hO μ hμ_one, μ'_zero O μ hμ_add]

theorem blk_congr_zero (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (h : ∀ i l, μ' O μ (y i l) = 0) :
    blk O μ y = 0 := by
  apply LinearMap.ext; intro w; funext i
  rw [blk_apply]; simp [h]

theorem blk_eq_zero_iff (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) :
    blk O μ y = 0 ↔ ∀ i l, μ' O μ (y i l) = 0 := by
  constructor
  · intro h i l
    ext p q

    have := congrFun (congrFun (LinearMap.congr_fun h (fun l' q' => if l' = l ∧ q' = q then 1 else 0)) i) p
    rw [blk_apply] at this
    simp only [LinearMap.zero_apply, Pi.zero_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Pi.add_apply] at this
    fin_cases l <;> fin_cases q <;> simpa [Fin.sum_univ_two] using this
  · exact blk_congr_zero O μ y

end Blk2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

end CentModN
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

namespace CentModN

open Matrix

variable {N : ℕ} [NeZero N]

section Lattice

theorem exists_nsmul_mem_of_mem_span {W : Type} [AddCommGroup W] [Module ℚ W] (S : Submodule ℤ W)
    (y : W) (hy : y ∈ Submodule.span ℚ (S : Set W)) : ∃ n : ℕ, 0 < n ∧ ((n : ℚ) • y) ∈ S := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine S.add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul,
        show ((m : ℕ) : ℚ) • ((n : ℚ) • x) = m • ((n : ℚ) • x) from Nat.cast_smul_eq_nsmul ℚ m _]
      exact S.nsmul_mem hnx m
    · rw [Nat.cast_mul, mul_smul,
        show ((n : ℕ) : ℚ) • ((m : ℚ) • y) = n • ((m : ℚ) • y) from Nat.cast_smul_eq_nsmul ℚ n _]
      exact S.nsmul_mem hmy n
  | smul q x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n * q.den, Nat.mul_pos hn q.den_pos, ?_⟩
    rw [Nat.cast_mul, smul_smul, mul_assoc, Rat.den_mul_eq_num, mul_comm, ← smul_smul]
    rw [show (q.num : ℚ) • ((n : ℚ) • x) = q.num • ((n : ℚ) • x) from (Int.cast_smul_eq_zsmul ℚ q.num _)]
    exact S.smul_mem q.num hnx

end Lattice
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

end CentModN
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

namespace CentModN

open Matrix

variable {N : ℕ} [NeZero N]

section Order

open scoped Quaternion
open QuaternionAlgebra

theorem isOrder_of_forall_iff {a₁ b₁ c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :
    IsOrder R where
  one_mem := by
    rw [hRiff]; intro i l
    rw [map_one, Matrix.one_apply]
    split_ifs
    · exact hO.one_mem
    · exact O.zero_mem
  mul_mem := by
    intro x y hx hy
    rw [hRiff] at hx hy ⊢
    intro i l
    rw [map_mul, Matrix.mul_apply]
    exact O.sum_mem fun k _ => hO.mul_mem (hx i k) (hy k l)
  spanTop := by
    rw [eq_top_iff]
    intro x _
    have hex : ∀ i l : Fin 2, ∃ n : ℕ, 0 < n ∧ ((n : ℚ) • τ x i l) ∈ O := fun i l =>
      exists_nsmul_mem_of_mem_span O _ (by rw [hO.spanTop]; trivial)
    choose n hn hnO using hex
    set M : ℕ := ∏ i, ∏ l, n i l with hM
    have hMpos : 0 < M := Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hn i l
    have hMx : ((M : ℚ) • x) ∈ R := by
      rw [hRiff]; intro i l
      rw [map_smul, Matrix.smul_apply]
      obtain ⟨k, hk⟩ : n i l ∣ M :=
        dvd_trans (Finset.dvd_prod_of_mem (fun l => n i l) (Finset.mem_univ l))
          (Finset.dvd_prod_of_mem (fun i => ∏ l, n i l) (Finset.mem_univ i))
      rw [hk, Nat.cast_mul, mul_comm, mul_smul,
        show ((k : ℕ) : ℚ) • ((n i l : ℚ) • τ x i l) = k • ((n i l : ℚ) • τ x i l) from Nat.cast_smul_eq_nsmul ℚ k _]
      exact O.nsmul_mem (hnO i l) k
    have hx : x = (M : ℚ)⁻¹ • ((M : ℚ) • x) := by
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hMpos.ne'), one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hMx)
  fg := by
    let f : ℍ[ℚ, a₁, b₁] →ₗ[ℤ] (Fin 2 → Fin 2 → ℍ[ℚ, c, d]) :=
      { toFun := fun x i l => τ x i l
        map_add' := fun x y => by funext i l; simp [map_add]
        map_smul' := fun z x => by
          funext i l
          show τ (z • x) i l = (z • fun i l => τ x i l) i l
          rw [map_zsmul τ]; rfl }
    have hf : Function.Injective f := fun x y h =>
      hτ (funext fun i => funext fun l => congrFun (congrFun h i) l)
    let MO : Submodule ℤ (Fin 2 → Fin 2 → ℍ[ℚ, c, d]) :=
      Submodule.pi Set.univ fun _ => Submodule.pi Set.univ fun _ => O
    have hMO : MO.FG := Submodule.fg_pi fun _ => Submodule.fg_pi fun _ => hO.fg
    have hle : R.map f ≤ MO := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MO, Submodule.mem_pi, Set.mem_univ, true_implies]
      intro i l; exact (hRiff x).1 hx i l
    haveI : IsNoetherian ℤ ↥MO := isNoetherian_of_fg_of_noetherian _ hMO
    have hfg : (R.map f).FG := by
      have h1 : ((R.map f).comap MO.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map MO.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
    exact Submodule.fg_of_fg_map_injective f hf hfg

end Order
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

section Blk3

open scoped Quaternion
open QuaternionAlgebra

variable {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
  (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
  (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)
  (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))

include hμ_add in
theorem blk_add (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O) :
    blk O μ (y + y') = blk O μ y + blk O μ y' := by
  apply LinearMap.ext; intro w; funext i
  rw [LinearMap.add_apply, blk_apply, blk_apply, blk_apply]
  simp only [Matrix.add_apply, Pi.add_apply, μ'_add O μ hμ_add _ _ (hy _ _) (hy' _ _), Matrix.add_mulVec,
    Finset.sum_add_distrib]

theorem N_smul_mem (o : ℍ[ℚ, c, d]) (ho : o ∈ O) : ((N : ℚ) • o) ∈ O := by
  rw [Nat.cast_smul_eq_nsmul]; exact O.nsmul_mem ho N

include hμ_ker in
theorem blk_N_smul (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) :
    blk O μ ((N : ℚ) • y) = 0 := by
  apply blk_congr_zero
  intro i l
  rw [Matrix.smul_apply, μ'_of_mem O μ _ (N_smul_mem O _ (hy i l))]
  exact (hμ_ker _).mpr ⟨⟨y i l, hy i l⟩, rfl⟩

end Blk3
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

end CentModN
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

namespace CentModN

open Matrix

section MainProof

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld

theorem main
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (hH' : IsDefiniteRamifiedExactlyAt c d r) (hOmax : IsMaximalOrder O)
    (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
    (hμ_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, μ ⟨1, h⟩ = 1)
    (hμ_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O), μ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = μ x * μ y)
    (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)
    (hμ_surj : Function.Surjective μ)
    (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :
    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R) (m : ↥Λ),
        blk O μ (τ x) * blk O μ (j (m : ℍ[ℚ, a, b])) = blk O μ (j (m : ℍ[ℚ, a, b])) * blk O μ (τ x)) ∧
    (∀ β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N),
        (∀ m : ↥Λ, β * blk O μ (j (m : ℍ[ℚ, a, b])) = blk O μ (j (m : ℍ[ℚ, a, b])) * β) →
        ∃ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R), β = blk O μ (τ x)) ∧
    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R), blk O μ (τ x) = 0 ↔ ∃ y ∈ R, x = (N : ℚ) • y) := by
  classical
  have hτO : ∀ x, x ∈ R → ∀ i l, τ x i l ∈ O := fun x hx => (hRiff x).1 hx

  have comm : ∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R) (m : ↥Λ),
      blk O μ (τ x) * blk O μ (j (m : ℍ[ℚ, a, b])) = blk O μ (j (m : ℍ[ℚ, a, b])) * blk O μ (τ x) := by
    intro x hx m
    rw [← blk_mul O hO μ hμ_mul hμ_add _ _ (hτO x hx) (hj m), ← blk_mul O hO μ hμ_mul hμ_add _ _ (hj m) (hτO x hx)]
    congr 1
    exact ((hτc (τ x)).mpr ⟨x, rfl⟩) m

  have ker_iff : ∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R), blk O μ (τ x) = 0 ↔ ∃ y ∈ R, x = (N : ℚ) • y := by
    intro x hx
    rw [blk_eq_zero_iff]
    constructor
    · intro h
      have hent : ∀ i l, ∃ o : ↥O, τ x i l = (N : ℚ) • (o : ℍ[ℚ, c, d]) := fun i l => by
        have := h i l
        rw [μ'_of_mem O μ _ (hτO x hx i l)] at this
        exact (hμ_ker _).mp this
      have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
      refine ⟨(N : ℚ)⁻¹ • x, ?_, ?_⟩
      · rw [hRiff]; intro i l
        obtain ⟨o, ho⟩ := hent i l
        rw [map_smul, Matrix.smul_apply, ho, smul_smul, inv_mul_cancel₀ hN0, one_smul]
        exact o.2
      · rw [smul_smul, mul_inv_cancel₀ hN0, one_smul]
    · rintro ⟨y, hy, rfl⟩ i l
      rw [map_smul, Matrix.smul_apply, μ'_of_mem O μ _ (N_smul_mem O _ (hτO y hy i l))]
      exact (hμ_ker _).mpr ⟨⟨τ y i l, hτO y hy i l⟩, rfl⟩
  refine ⟨comm, ?_, ker_iff⟩

  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd hB Λ hΛ N hrN hrbarN
  have hΛO : IsOrder Λ := hΛ.1
  have hjN : ∀ y : ↥Λ, blk O μ (j ((N : ℚ) • (y : ℍ[ℚ, a, b]))) = 0 := fun y => by
    rw [map_smul]; exact blk_N_smul O μ hμ_ker _ (hj y)
  have ψ_wd : ∀ m m' : ↥Λ, φ m = φ m' → blk O μ (j (m : ℍ[ℚ, a, b])) = blk O μ (j (m' : ℍ[ℚ, a, b])) := by
    intro m m' h
    have h0 : φ (m - m') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨y, hy⟩ := (hφker _).mp h0
    have hsplit : j (m : ℍ[ℚ, a, b]) = j (m' : ℍ[ℚ, a, b]) + j ((N : ℚ) • (y : ℍ[ℚ, a, b])) := by
      rw [← map_add, ← hy, Submodule.coe_sub, add_sub_cancel]
    rw [hsplit, blk_add O μ hμ_add _ _ (hj m') (fun i l => ?_), hjN, add_zero]
    rw [map_smul, Matrix.smul_apply]; exact N_smul_mem O _ (hj y i l)

  let s : Matrix (Fin 2) (Fin 2) (ZMod N) → ↥Λ := Function.surjInv hφsurj
  have hs : ∀ A, φ (s A) = A := Function.surjInv_eq hφsurj
  let α' : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N) :=
    { toFun := fun A => blk O μ (j (s A : ℍ[ℚ, a, b]))
      map_one' := by
        have : φ (s 1) = φ ⟨1, hΛO.one_mem⟩ := by rw [hs, hφ1]
        show blk O μ (j (s 1 : ℍ[ℚ, a, b])) = 1
        rw [ψ_wd _ _ this]
        show blk O μ (j 1) = 1
        rw [map_one, blk_one O hO μ hμ_one hμ_add]
      map_mul' := fun A B => by
        have hmem : ((s A : ℍ[ℚ, a, b]) * (s B : ℍ[ℚ, a, b])) ∈ Λ := hΛO.mul_mem (s A).2 (s B).2
        have : φ (s (A * B)) = φ ⟨_, hmem⟩ := by rw [hs, hφmul, hs, hs]
        show blk O μ (j (s (A * B) : ℍ[ℚ, a, b])) = blk O μ (j (s A : ℍ[ℚ, a, b])) * blk O μ (j (s B : ℍ[ℚ, a, b]))
        rw [ψ_wd _ _ this]
        show blk O μ (j ((s A : ℍ[ℚ, a, b]) * (s B : ℍ[ℚ, a, b]))) = _
        rw [map_mul, blk_mul O hO μ hμ_mul hμ_add _ _ (hj _) (hj _)]
      map_zero' := by
        have : φ (s 0) = φ 0 := by rw [hs, map_zero]
        show blk O μ (j (s 0 : ℍ[ℚ, a, b])) = 0
        rw [ψ_wd _ _ this]
        show blk O μ (j ((0 : ↥Λ) : ℍ[ℚ, a, b])) = 0
        rw [Submodule.coe_zero, map_zero]
        exact blk_congr_zero O μ 0 fun i l => by rw [Matrix.zero_apply]; exact μ'_zero O μ hμ_add
      map_add' := fun A B => by
        have : φ (s (A + B)) = φ (s A + s B) := by rw [hs, map_add, hs, hs]
        show blk O μ (j (s (A + B) : ℍ[ℚ, a, b])) = blk O μ (j (s A : ℍ[ℚ, a, b])) + blk O μ (j (s B : ℍ[ℚ, a, b]))
        rw [ψ_wd _ _ this]
        show blk O μ (j (((s A + s B) : ↥Λ) : ℍ[ℚ, a, b])) = _
        rw [Submodule.coe_add, map_add, blk_add O μ hμ_add _ _ (hj _) (hj _)] }
  have α'_φ : ∀ m : ↥Λ, α' (φ m) = blk O μ (j (m : ℍ[ℚ, a, b])) := fun m => ψ_wd _ _ (hs (φ m))

  have hV : Nat.card (Fin 2 → Fin 2 → ZMod N) = N ^ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi, Fin.prod_univ_two, Fintype.card_pi, Fin.prod_univ_two, ZMod.card]; ring
  obtain ⟨v₀, hv₀⟩ := Matrix.exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq N hN (Fin 2 → Fin 2 → ZMod N) hV α'
  have hC := card_centralizer α' v₀ hv₀

  have hRord : IsOrder R := isOrder_of_forall_iff O hO τ hτ R hRiff
  let Φ : ↥R →+ Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N) :=
    { toFun := fun x => blk O μ (τ (x : ℍ[ℚ, a₁, b₁]))
      map_zero' := by
        show blk O μ (τ 0) = 0
        rw [map_zero]; exact blk_congr_zero O μ 0 fun i l => by rw [Matrix.zero_apply]; exact μ'_zero O μ hμ_add
      map_add' := fun x y => by
        show blk O μ (τ ((x : ℍ[ℚ, a₁, b₁]) + y)) = blk O μ (τ (x : ℍ[ℚ, a₁, b₁])) + blk O μ (τ (y : ℍ[ℚ, a₁, b₁]))
        rw [map_add, blk_add O μ hμ_add _ _ (hτO _ x.2) (hτO _ y.2)] }
  have hΦ : ∀ x : ↥R, Φ x = blk O μ (τ (x : ℍ[ℚ, a₁, b₁])) := fun x => rfl
  have hrange : ∀ x : ↥R, Φ x ∈ Subalgebra.centralizer (ZMod N) (Set.range α') := by
    intro x
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    obtain ⟨m, rfl⟩ := hφsurj A
    rw [α'_φ, hΦ]
    exact (comm x x.2 m).symm

  set K : Submodule ℤ ℍ[ℚ, a₁, b₁] :=
    Submodule.span ℤ ((fun y : ℍ[ℚ, a₁, b₁] => (N : ℤ) • y) '' (R : Set ℍ[ℚ, a₁, b₁])) with hKdef
  have hK' : K = R.map ((N : ℤ) • (LinearMap.id : ℍ[ℚ, a₁, b₁] →ₗ[ℤ] ℍ[ℚ, a₁, b₁])) := by
    rw [hKdef]
    have : ((fun y : ℍ[ℚ, a₁, b₁] => (N : ℤ) • y) '' (R : Set ℍ[ℚ, a₁, b₁])) =
        (R.map ((N : ℤ) • (LinearMap.id : ℍ[ℚ, a₁, b₁] →ₗ[ℤ] ℍ[ℚ, a₁, b₁])) : Set ℍ[ℚ, a₁, b₁]) := by
      ext z; simp [Submodule.map_coe]
    rw [this, Submodule.span_eq]
  have hKmem : ∀ z : ℍ[ℚ, a₁, b₁], z ∈ K ↔ ∃ y ∈ R, z = (N : ℚ) • y := by
    intro z
    rw [hK', Submodule.mem_map]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]⟩
  have hker : Φ.ker = K.toAddSubgroup.addSubgroupOf R.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hΦ, ker_iff _ x.2]
    show (∃ y ∈ R, (x : ℍ[ℚ, a₁, b₁]) = (N : ℚ) • y) ↔ (x : ℍ[ℚ, a₁, b₁]) ∈ K
    rw [hKmem]
  have hidx := QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hRord N (NeZero.pos N)
  have hcardRange : Nat.card ↥(Φ.range) = N ^ 4 := by
    rw [← hidx, AddSubgroup.relIndex, ← hKdef, ← hker, AddSubgroup.index]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Φ).toEquiv.symm

  haveI : Finite (Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) :=
    Finite.of_injective (fun f : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N) => (f : (Fin 2 → Fin 2 → ZMod N) → _))
      (fun f g h => LinearMap.ext (congrFun h))
  have hsub : ((Φ.range : AddSubgroup _) : Set (Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))) ⊆
      (Subalgebra.centralizer (ZMod N) (Set.range α') : Set _) := by
    rintro β ⟨x, rfl⟩; exact hrange x
  have heq : ((Φ.range : AddSubgroup _) : Set (Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))) =
      (Subalgebra.centralizer (ZMod N) (Set.range α') : Set _) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    show Nat.card ↥(Subalgebra.centralizer (ZMod N) (Set.range α')) ≤ Nat.card ↥(Φ.range)
    rw [hC, hcardRange]

  intro β hβ
  have hβC : β ∈ (Subalgebra.centralizer (ZMod N) (Set.range α') : Set _) := by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    obtain ⟨m, rfl⟩ := hφsurj A
    rw [α'_φ]; exact (hβ m).symm
  rw [← heq] at hβC
  obtain ⟨x, hx⟩ := hβC
  exact ⟨x, x.2, by rw [← hx]; rfl⟩

end MainProof
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

end CentModN
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder.CentModN"

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld

open CentModN in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (hH' : IsDefiniteRamifiedExactlyAt c d r) (hOmax : IsMaximalOrder O)

    (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
    (hμ_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, μ ⟨1, h⟩ = 1)
    (hμ_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O), μ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = μ x * μ y)
    (hμ_add : ∀ x y : ↥O, μ (x + y) = μ x + μ y)
    (hμ_surj : Function.Surjective μ)
    (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :

    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R) (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N),
        (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) ((fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) l)) =
          (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) l))) ∧

    (∀ β : (Fin 2 → Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → Fin 2 → ZMod N),
        (∀ (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N),
            β (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) = (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((β w) l))) →
        ∃ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R), ∀ w : Fin 2 → Fin 2 → ZMod N, β w = (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l))) ∧

    (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R),
        (∀ w : Fin 2 → Fin 2 → ZMod N, (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) = 0) ↔
          ∃ y ∈ R, x = (N : ℚ) • y) := by
  obtain ⟨hI, hII, hIII⟩ := CentModN.main hrr hrN hrbarN hN hB Λ hΛ O hO hH' hOmax μ hμ_one hμ_mul hμ_add hμ_surj hμ_ker
    j hj hdef τ hτ hτc R hRiff
  refine ⟨?_, ?_, ?_⟩
  · intro x hx m w
    have e1 : (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) =
        blk O μ (j (m : ℍ[ℚ, a, b])) w := blk_eq O μ _ (hj m) w
    have e2 : (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) =
        blk O μ (τ x) w := blk_eq O μ _ ((hRiff x).1 hx) w
    rw [e1, e2]
    have e3 : (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) ((blk O μ (j (m : ℍ[ℚ, a, b])) w) l)) =
        blk O μ (τ x) (blk O μ (j (m : ℍ[ℚ, a, b])) w) := blk_eq O μ _ ((hRiff x).1 hx) _
    have e4 : (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) ((blk O μ (τ x) w) l)) =
        blk O μ (j (m : ℍ[ℚ, a, b])) (blk O μ (τ x) w) := blk_eq O μ _ (hj m) _
    rw [e3, e4, ← Module.End.mul_apply, ← Module.End.mul_apply, hI x hx m]
  · intro β hβ
    have hβ' : ∀ m : ↥Λ, β * blk O μ (j (m : ℍ[ℚ, a, b])) = blk O μ (j (m : ℍ[ℚ, a, b])) * β := by
      intro m
      apply LinearMap.ext; intro w
      rw [Module.End.mul_apply, Module.End.mul_apply, ← blk_eq O μ _ (hj m) w, hβ m w, blk_eq O μ _ (hj m)]
    obtain ⟨x, hx, hβx⟩ := hII β hβ'
    refine ⟨x, hx, fun w => ?_⟩
    rw [hβx, blk_eq O μ _ ((hRiff x).1 hx) w]
  · intro x hx
    rw [← hIII x hx]
    constructor
    · intro h
      apply LinearMap.ext; intro w
      rw [LinearMap.zero_apply, ← blk_eq O μ _ ((hRiff x).1 hx) w]; exact h w
    · intro h w
      rw [blk_eq O μ _ ((hRiff x).1 hx) w, h, LinearMap.zero_apply]

end S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_forall_commute_and_forall_exists_eq_blk_and_blk_eq_zero_iff_of_centraliser_of_isMaximalOrder (solution)
