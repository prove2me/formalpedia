-- Prove2me | solution 1 for Deformation.DieudonneDatum.exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2a7c5a2e-489e-5b6a-aabc-f4e3c2c5fd10

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
import Theorems.Thm_Deformation_DieudonneModule_map_surjective_and_exact_map_of_ker_eq_map_ker_counit
import Theorems.Thm_Deformation_DieudonneModule_exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
p2m_attr_erase "instance" "Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open Function
open scoped TensorProduct

namespace DieudonneTowerZMod

section HopfIdeals

p2m_open "Coalgebra Bialgebra WithConv PDivisibleGroup HopfAlgebra~augIdeal"

variable {R : Type*} [CommRing R]
variable {H : Type*} [CommRing H] [HopfAlgebra R H]
variable {H' : Type*} [CommRing H'] [HopfAlgebra R H']
variable {B : Type*} [CommRing B] [HopfAlgebra R B]

theorem isHopfIdeal_span (T : Set H)
    (hΔ : ∀ x ∈ T, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span T))
        (Ideal.Quotient.mkₐ R (Ideal.span T)) (comul (R := R) x) = 0)
    (hε : ∀ x ∈ T, counit (R := R) x = 0)
    (hS : ∀ x ∈ T, antipode R x ∈ Ideal.span T) :
    (Ideal.span T).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero := by
    intro x hx
    let F : H →ₐ[R] (H ⧸ Ideal.span T) ⊗[R] (H ⧸ Ideal.span T) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span T))
        (Ideal.Quotient.mkₐ R (Ideal.span T))).comp (comulAlgHom R H)
    change F x = 0
    induction hx using Submodule.span_induction with
    | mem y hy => exact hΔ y hy
    | zero => exact map_zero F
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_eq_mul, map_mul, hy, mul_zero]
  counit_eq_zero := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hε y hy
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_eq_mul, Bialgebra.counit_mul, hy, mul_zero]
  antipode_mem := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Ideal.add_mem _ hy hz
    | smul a y _ hy =>
      rw [smul_eq_mul, ← antipodeAlgHom_apply, map_mul]
      exact Ideal.mul_mem_left _ _ hy

theorem isHopfIdeal_ker_of_surjective (φ : H →ₐc[R] B) (hφ : Function.Surjective φ) :
    (RingHom.ker (φ : H →ₐ[R] B)).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero := by
    intro x hx
    have hx0 : φ x = 0 := hx
    let e : (H ⧸ RingHom.ker (φ : H →ₐ[R] B)) ≃ₐ[R] B := Ideal.quotientKerAlgEquivOfSurjective hφ
    have hmk : Ideal.Quotient.mkₐ R (RingHom.ker (φ : H →ₐ[R] B)) =
        ((e.symm : B →ₐ[R] H ⧸ RingHom.ker (φ : H →ₐ[R] B)).comp (φ : H →ₐ[R] B)) := by
      refine AlgHom.ext fun y => ?_
      rw [AlgHom.comp_apply]
      change Ideal.Quotient.mk (RingHom.ker (φ : H →ₐ[R] B)) y = e.symm (φ y)
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      exact Ideal.quotientKerAlgEquivOfSurjective_mk hφ y
    rw [hmk, Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
    have hco : Algebra.TensorProduct.map (φ : H →ₐ[R] B) (φ : H →ₐ[R] B) (comul (R := R) x) =
        comul (R := R) (φ x) :=
      (DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom φ) x)
    rw [hco, hx0, map_zero, map_zero]
  counit_eq_zero := by
    intro x hx
    have hx0 : φ x = 0 := hx
    rw [← Hopf.counit_bialgHom_apply φ x, hx0, map_zero]
  antipode_mem := by
    intro x hx
    have hx0 : φ x = 0 := hx
    change φ (antipode R x) = 0
    rw [HopfAlgebra.map_antipode φ, hx0, map_zero]

theorem isHopfIdeal_map (ψ : H →ₐc[R] H') (I : Ideal H) [hI : I.IsHopfIdeal' R] :
    (I.map (ψ : H →ₐ[R] H')).IsHopfIdeal' R := by
  have hspan : Ideal.span ((ψ : H →ₐ[R] H') '' (I : Set H)) = I.map (ψ : H →ₐ[R] H') := rfl
  rw [← hspan]
  refine isHopfIdeal_span _ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    set J : Ideal H' := Ideal.span ((ψ : H →ₐ[R] H') '' (I : Set H)) with hJ
    have hIJ : I ≤ J.comap (ψ : H →ₐ[R] H') := by
      intro y hy
      exact Ideal.subset_span ⟨y, hy, rfl⟩
    let ψbar : (H ⧸ I) →ₐ[R] (H' ⧸ J) := Ideal.quotientMapₐ J (ψ : H →ₐ[R] H') hIJ
    have hmk : (Ideal.Quotient.mkₐ R J).comp (ψ : H →ₐ[R] H') = ψbar.comp (Ideal.Quotient.mkₐ R I) :=
      (Ideal.quotient_map_comp_mkₐ J (ψ : H →ₐ[R] H') hIJ).symm
    have hco : comul (R := R) ((ψ : H →ₐ[R] H') x) =
        Algebra.TensorProduct.map (ψ : H →ₐ[R] H') (ψ : H →ₐ[R] H') (comul (R := R) x) :=
      (DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom ψ) x).symm
    change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (Ideal.Quotient.mkₐ R J)
      (comul (R := R) ((ψ : H →ₐ[R] H') x)) = 0
    rw [hco, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hmk, Algebra.TensorProduct.map_comp,
      AlgHom.comp_apply, hI.map_mkₐ_comul_eq_zero x hx, map_zero]
  · rintro _ ⟨x, hx, rfl⟩
    change counit (R := R) (ψ x) = 0
    rw [Hopf.counit_bialgHom_apply, hI.counit_eq_zero x hx]
  · rintro _ ⟨x, hx, rfl⟩
    change antipode R (ψ x) ∈ _
    rw [← HopfAlgebra.map_antipode ψ]
    exact Ideal.subset_span ⟨_, hI.antipode_mem x hx, rfl⟩

scoped instance isHopfIdeal_augIdeal : (Hopf.augIdeal R H).IsHopfIdeal' R := by
  have h : Hopf.augIdeal R H =
      RingHom.ker ((Bialgebra.counitBialgHom R H : H →ₐc[R] R) : H →ₐ[R] R) := rfl
  rw [h]
  exact isHopfIdeal_ker_of_surjective _ (Bialgebra.counit_surjective (R := R) (A := H))

scoped instance isHopfIdeal_torsionIdeal [Coalgebra.IsCocomm R H] (n : ℕ) :
    (Hopf.torsionIdeal R H n).IsHopfIdeal' R := by
  have h : Hopf.torsionIdeal R H n =
      (Hopf.augIdeal R H).map ((Hopf.nsmulBialgHom R H n : H →ₐc[R] H) : H →ₐ[R] H) := by
    rw [Hopf.toAlgHom_nsmulBialgHom]
    rfl
  rw [h]
  exact isHopfIdeal_map _ _

end HopfIdeals

section NSMul

open Deformation PDivisibleGroup

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
variable {A : Type*} [CommRing A] [Bialgebra R A]

theorem map_nsmulAlgHom_of_mem_wittHom {m : ℕ} (n : ℕ) {x : TruncatedWittVector p m A}
    (hx : x ∈ wittHom R p m A) :
    TruncWitt.map (Hopf.nsmulAlgHom R A n).toRingHom x = n • x := by
  induction n with
  | zero =>
    rw [Hopf.nsmulAlgHom_zero, zero_smul]
    have hc : ((Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)).toRingHom =
        (algebraMap R A).comp (Bialgebra.counitAlgHom R A).toRingHom := rfl
    rw [hc, ← TruncWitt.map_map, map_counit_of_mem_wittHom hx, map_zero]
  | succ n ih =>
    rw [Hopf.nsmulAlgHom_succ, add_smul, one_smul, ← ih]
    have h := map_convMul_of_mem_wittHom (T := A) hx (WithConv.toConv (Hopf.nsmulAlgHom R A n))
      (WithConv.toConv (AlgHom.id R A))
    rw [h]
    congr 1
    exact TruncWitt.map_id x

variable [Coalgebra.IsCocomm R A]

theorem map_nsmulBialgHom (n : ℕ) (z : DieudonneModule R p A) :
    DieudonneModule.map R p (Hopf.nsmulBialgHom R A n) z = n • z := by
  induction z using DieudonneModule.induction_on with
  | ih m x =>
    rw [DieudonneModule.map_of, ← map_nsmul]
    congr 1
    refine Subtype.ext ?_
    rw [coe_wittHomMap, Hopf.toAlgHom_nsmulBialgHom, AddSubgroupClass.coe_nsmul]
    exact map_nsmulAlgHom_of_mem_wittHom p n x.2

end NSMul

section Levels

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) (r : ℕ)

def P (m : ℕ) : Submodule 𝓞 (Fin r → 𝓞) :=
  LinearMap.range ((p : 𝓞) ^ m • (LinearMap.id : (Fin r → 𝓞) →ₗ[𝓞] (Fin r → 𝓞)))

variable {𝓞 p r}

theorem mem_P {m : ℕ} {x : Fin r → 𝓞} : x ∈ P 𝓞 p r m ↔ ∃ y, x = (p : 𝓞) ^ m • y := by
  simp only [P, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

theorem smul_mem_P (m : ℕ) (y : Fin r → 𝓞) : (p : 𝓞) ^ m • y ∈ P 𝓞 p r m := mem_P.2 ⟨y, rfl⟩

theorem P_zero : P 𝓞 p r 0 = ⊤ := by
  refine eq_top_iff.2 fun x _ => mem_P.2 ⟨x, ?_⟩
  rw [pow_zero, one_smul]

theorem P_succ_le (m : ℕ) : P 𝓞 p r (m + 1) ≤ P 𝓞 p r m := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_P.1 hx
  exact mem_P.2 ⟨(p : 𝓞) • y, by rw [pow_succ, mul_smul]⟩

theorem P_le_of_le {m n : ℕ} (h : m ≤ n) : P 𝓞 p r n ≤ P 𝓞 p r m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (P_succ_le _).trans ih

theorem eq_zero_of_pow_smul_eq_zero (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (m : ℕ)
    {z : Fin r → 𝓞} (hz : (p : 𝓞) ^ m • z = 0) : z = 0 := by
  have hpm : (p : 𝓞) ^ m ∈ nonZeroDivisors 𝓞 := pow_mem hp m
  funext i
  have hi := congr_fun hz i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mem_nonZeroDivisors_iff_right.1 hpm) (z i) (by rw [mul_comm]; exact hi)

theorem pow_smul_injective (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (m : ℕ) :
    Function.Injective fun z : Fin r → 𝓞 => (p : 𝓞) ^ m • z := by
  intro z w h
  have h' : (p : 𝓞) ^ m • (z - w) = 0 := by
    have h : (p : 𝓞) ^ m • z = (p : 𝓞) ^ m • w := h
    rw [smul_sub, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_pow_smul_eq_zero hp m h')

section Card

variable [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})

include hker

theorem card_quot_P_one : Nat.card ((Fin r → 𝓞) ⧸ P 𝓞 p r 1) = p ^ r := by
  let f : (Fin r → 𝓞) →ₗ[𝓞] (Fin r → ZMod p) := (Algebra.linearMap 𝓞 (ZMod p)).compLeft (Fin r)
  have hf : Function.Surjective f :=
    (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p))).comp_left
  have hkerf : LinearMap.ker f = P 𝓞 p r 1 := by
    ext x
    rw [LinearMap.mem_ker, mem_P]
    constructor
    · intro hx
      have hxi : ∀ i, ∃ y : 𝓞, x i = (p : 𝓞) * y := by
        intro i
        have h0 : algebraMap 𝓞 (ZMod p) (x i) = 0 := congr_fun hx i
        have h1 : x i ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)) := h0
        rw [hker, Ideal.mem_span_singleton'] at h1
        obtain ⟨a, ha⟩ := h1
        exact ⟨a, by rw [← ha, mul_comm]⟩
      choose y hy using hxi
      refine ⟨y, funext fun i => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, pow_one]
      exact hy i
    · rintro ⟨y, rfl⟩
      funext i
      change algebraMap 𝓞 (ZMod p) (((p : 𝓞) ^ 1 • y) i) = 0
      rw [Pi.smul_apply, smul_eq_mul, map_mul, pow_one]
      have hp0 : algebraMap 𝓞 (ZMod p) (p : 𝓞) = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact Ideal.mem_span_singleton_self _
      rw [hp0, zero_mul]
  have e : ((Fin r → 𝓞) ⧸ P 𝓞 p r 1) ≃ₗ[𝓞] (Fin r → ZMod p) :=
    (Submodule.quotEquivOfEq _ _ hkerf.symm).trans (f.quotKerEquivOfSurjective hf)
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_quot_P (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (m : ℕ) :
    Nat.card ((Fin r → 𝓞) ⧸ P 𝓞 p r m) = p ^ (m * r) := by
  induction m with
  | zero =>
    rw [zero_mul, pow_zero, P_zero]
    exact Nat.card_unique
  | succ m ih =>

    let g : (Fin r → 𝓞) →ₗ[𝓞] (Fin r → 𝓞) ⧸ P 𝓞 p r (m + 1) :=
      (P 𝓞 p r (m + 1)).mkQ ∘ₗ ((p : 𝓞) ^ m • LinearMap.id)
    have hrange : LinearMap.range g = (P 𝓞 p r m).map (P 𝓞 p r (m + 1)).mkQ := LinearMap.range_comp _ _
    have hkerg : LinearMap.ker g = P 𝓞 p r 1 := by
      ext x
      rw [LinearMap.mem_ker, mem_P]
      change (P 𝓞 p r (m + 1)).mkQ ((p : 𝓞) ^ m • x) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_P]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, pow_smul_injective hp m ?_⟩
        change (p : 𝓞) ^ m • x = (p : 𝓞) ^ m • ((p : 𝓞) ^ 1 • y)
        rw [hy, pow_one, ← mul_smul, ← pow_succ]
      · rintro ⟨y, rfl⟩
        exact ⟨y, by rw [pow_one, ← mul_smul, ← pow_succ]⟩
    have hS : Nat.card ((P 𝓞 p r m).map (P 𝓞 p r (m + 1)).mkQ) = p ^ r := by
      rw [← hrange, ← Nat.card_congr g.quotKerEquivRange.toEquiv,
        Nat.card_congr (Submodule.quotEquivOfEq _ _ hkerg).toEquiv]
      exact card_quot_P_one hker
    have hQ : Nat.card (((Fin r → 𝓞) ⧸ P 𝓞 p r (m + 1)) ⧸ (P 𝓞 p r m).map (P 𝓞 p r (m + 1)).mkQ) =
        p ^ (m * r) := by
      rw [Nat.card_congr (Submodule.quotientQuotientEquivQuotient _ _ (P_succ_le m)).toEquiv]
      exact ih
    rw [Submodule.card_eq_card_quotient_mul_card ((P 𝓞 p r m).map (P 𝓞 p r (m + 1)).mkQ), hS, hQ,
      ← pow_add, Nat.succ_mul, add_comm]

end Card

variable (D₁ : Deformation.DieudonneDatum (p : 𝓞) (Fin r → 𝓞))

theorem P_le_comap_F (m : ℕ) : P 𝓞 p r m ≤ (P 𝓞 p r m).comap D₁.F := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_P.1 hx
  change D₁.F ((p : 𝓞) ^ m • y) ∈ P 𝓞 p r m
  rw [map_smul]
  exact smul_mem_P m _

theorem P_le_comap_V (m : ℕ) : P 𝓞 p r m ≤ (P 𝓞 p r m).comap D₁.V := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_P.1 hx
  change D₁.V ((p : 𝓞) ^ m • y) ∈ P 𝓞 p r m
  rw [map_smul]
  exact smul_mem_P m _

def quotF (m : ℕ) : ((Fin r → 𝓞) ⧸ P 𝓞 p r m) →ₗ[𝓞] ((Fin r → 𝓞) ⧸ P 𝓞 p r m) :=
  (P 𝓞 p r m).mapQ (P 𝓞 p r m) D₁.F (P_le_comap_F D₁ m)

def quotV (m : ℕ) : ((Fin r → 𝓞) ⧸ P 𝓞 p r m) →ₗ[𝓞] ((Fin r → 𝓞) ⧸ P 𝓞 p r m) :=
  (P 𝓞 p r m).mapQ (P 𝓞 p r m) D₁.V (P_le_comap_V D₁ m)

@[scoped simp] theorem quotF_mk (m : ℕ) (x : Fin r → 𝓞) :
    quotF D₁ m (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D₁.F x) :=
  Submodule.mapQ_apply _ _ _ _

@[scoped simp] theorem quotV_mk (m : ℕ) (x : Fin r → 𝓞) :
    quotV D₁ m (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D₁.V x) :=
  Submodule.mapQ_apply _ _ _ _

def quotDatum (m : ℕ) : Deformation.DieudonneDatum (p : ℤ) ((Fin r → 𝓞) ⧸ P 𝓞 p r m) where
  F := (quotF D₁ m).toAddMonoidHom.toIntLinearMap
  V := (quotV D₁ m).toAddMonoidHom.toIntLinearMap
  fv := by
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      change quotF D₁ m (quotV D₁ m (Submodule.Quotient.mk x)) = (p : ℤ) • Submodule.Quotient.mk x
      rw [quotV_mk, quotF_mk, D₁.F_V_apply, Submodule.Quotient.mk_smul, Nat.cast_smul_eq_nsmul,
        natCast_zsmul]
  vf := by
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      change quotV D₁ m (quotF D₁ m (Submodule.Quotient.mk x)) = (p : ℤ) • Submodule.Quotient.mk x
      rw [quotF_mk, quotV_mk, D₁.V_F_apply, Submodule.Quotient.mk_smul, Nat.cast_smul_eq_nsmul,
        natCast_zsmul]

@[scoped simp] theorem quotDatum_F_mk (m : ℕ) (x : Fin r → 𝓞) :
    (quotDatum D₁ m).F (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D₁.F x) :=
  quotF_mk D₁ m x

@[scoped simp] theorem quotDatum_V_mk (m : ℕ) (x : Fin r → 𝓞) :
    (quotDatum D₁ m).V (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D₁.V x) :=
  quotV_mk D₁ m x

theorem exists_V_pow_mul_eq {N : ℕ} (hV : ∀ x, ∃ y, (D₁.V ^ N) x = (p : 𝓞) • y) (k : ℕ) (x : Fin r → 𝓞) :
    ∃ y, (D₁.V ^ (N * k)) x = (p : 𝓞) ^ k • y := by
  induction k generalizing x with
  | zero => exact ⟨x, by rw [mul_zero, pow_zero, pow_zero, one_smul]; rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := hV x
    obtain ⟨z, hz⟩ := ih y
    refine ⟨z, ?_⟩
    rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hy, map_smul, hz, ← mul_smul, ← pow_succ']

theorem quotDatum_V_pow_mk (m n : ℕ) (x : Fin r → 𝓞) :
    ((quotDatum D₁ m).V ^ n) (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((D₁.V ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, quotDatum_V_mk, pow_succ', Module.End.mul_apply]

theorem isNilpotent_quotDatum_V (hV : ∃ N : ℕ, ∀ x, ∃ y, (D₁.V ^ N) x = (p : 𝓞) • y) (m : ℕ) :
    IsNilpotent (quotDatum D₁ m).V := by
  obtain ⟨N, hN⟩ := hV
  refine ⟨N * m, LinearMap.ext fun z => ?_⟩
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨y, hy⟩ := exists_V_pow_mul_eq D₁ hN m x
    rw [quotDatum_V_pow_mk, hy, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact smul_mem_P m y

end Levels

section TwoSurjections

variable {M N N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']

def equivOfSurjective (ψ : M →+ N) (π : M →+ N') (hψ : Function.Surjective ψ)
    (hπ : Function.Surjective π) (h : ψ.ker = π.ker) : N ≃+ N' :=
  (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq h).trans (QuotientAddGroup.quotientKerEquivOfSurjective π hπ))

theorem equivOfSurjective_apply (ψ : M →+ N) (π : M →+ N') (hψ : Function.Surjective ψ)
    (hπ : Function.Surjective π) (h : ψ.ker = π.ker) (x : M) :
    equivOfSurjective ψ π hψ hπ h (ψ x) = π x := by
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ x) =
      (QuotientAddGroup.mk x : M ⧸ ψ.ker) := (AddEquiv.symm_apply_eq _).2 rfl
  change QuotientAddGroup.quotientKerEquivOfSurjective π hπ (QuotientAddGroup.quotientAddEquivOfEq h
    ((QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ x))) = π x
  rw [h1]
  rfl

end TwoSurjections

section Tower

p2m_open "Deformation PDivisibleGroup HopfAlgebra~augIdeal"

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (r : ℕ) (D₁ : Deformation.DieudonneDatum (p : 𝓞) (Fin r → 𝓞))
  (hV : ∃ N : ℕ, ∀ x, ∃ y, (D₁.V ^ N) x = (p : 𝓞) • y)

structure Stage (v : ℕ) where

  B : Type
  [instCR : CommRing B]
  [instHA : HopfAlgebra (ZMod p) B]
  [instCC : Coalgebra.IsCocomm (ZMod p) B]
  [instMF : Module.Finite (ZMod p) B]
  unip : IsLocalRing (CartierDual (ZMod p) B)
  rank : Module.finrank (ZMod p) B = p ^ (v * r)

  π : (Fin r → 𝓞) →+ DieudonneModule (ZMod p) p B
  surj : Function.Surjective π
  ker_iff : ∀ x, π x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y
  map_F : ∀ x, π (D₁.F x) = DieudonneModule.frobenius (ZMod p) p B (π x)
  map_V : ∀ x, π (D₁.V x) = DieudonneModule.verschiebung (ZMod p) p B (π x)

attribute [scoped instance] Stage.instCR Stage.instHA Stage.instCC Stage.instMF

structure Next (v : ℕ) (S : Stage p r D₁ v) where

  T : Stage p r D₁ (v + 1)

  s : T.B →ₐc[ZMod p] S.B
  surj : Function.Surjective s
  ker : RingHom.ker s = Hopf.torsionIdeal (ZMod p) T.B (p ^ v)
  compat : ∀ x, DieudonneModule.map (ZMod p) p s (T.π x) = S.π x

variable {p r D₁}

private theorem _root_.DieudonneTowerZMod.two_le : 2 ≤ p := (Fact.out : p.Prime).two_le

p2m_export "DieudonneTowerZMod" "two_le"

theorem finrank_eq_of_natCard (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing (CartierDual (ZMod p) B)) {n : ℕ}
    (hcard : Nat.card (DieudonneModule (ZMod p) p B) = p ^ n) :
    Module.finrank (ZMod p) B = p ^ n := by
  obtain ⟨L, hL1, hL2⟩ :=
    DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual (ZMod p) p B hB
  rw [Nat.card_zmod, hcard] at hL2
  rw [hL1, ← Nat.pow_right_injective (two_le (p := p)) hL2]

include hker in

theorem nonempty_stage_zero : Nonempty (Stage p r D₁ 0) := by
  let M0 : DieudonneDatum (p : ℤ) PUnit.{u + 1} :=
    { F := 0, V := 0, fv := Subsingleton.elim _ _, vf := Subsingleton.elim _ _ }
  obtain ⟨B, _, _, _, _, hB, e, -, -⟩ :=
    DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent p M0 IsNilpotent.zero
  haveI : Subsingleton (DieudonneModule (ZMod p) p B) := e.toEquiv.subsingleton
  have hcard : Nat.card (DieudonneModule (ZMod p) p B) = p ^ 0 := by rw [pow_zero]; exact Nat.card_unique
  refine ⟨{ B := B, unip := hB, rank := ?_, π := 0, surj := ?_, ker_iff := ?_, map_F := ?_, map_V := ?_ }⟩
  · rw [zero_mul]; exact finrank_eq_of_natCard B hB hcard
  · intro z; exact ⟨0, Subsingleton.elim _ _⟩
  · intro x; exact ⟨fun _ => ⟨x, by rw [pow_zero, one_smul]⟩, fun _ => rfl⟩
  · intro x; exact (map_zero _).symm
  · intro x; exact (map_zero _).symm

include hp hker hV in

theorem nonempty_next (v : ℕ) (S : Stage p r D₁ v) : Nonempty (Next p r D₁ v S) := by
  classical

  have hcardD : Nat.card ((Fin r → 𝓞) ⧸ P 𝓞 p r (v + 1)) = p ^ ((v + 1) * r) := card_quot_P hker hp (v + 1)
  haveI : Finite ((Fin r → 𝓞) ⧸ P 𝓞 p r (v + 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardD]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨C, _, _, _, _, hC, e, heF, heV⟩ :=
    DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent p
      (quotDatum D₁ (v + 1)) (isNilpotent_quotDatum_V D₁ hV (v + 1))

  let ρ : (Fin r → 𝓞) →+ DieudonneModule (ZMod p) p C :=
    e.symm.toAddMonoidHom.comp (P 𝓞 p r (v + 1)).mkQ.toAddMonoidHom
  have hρ_apply : ∀ x, ρ x = e.symm (Submodule.Quotient.mk x) := fun x => rfl
  have hρsurj : Function.Surjective ρ := by
    intro z
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (P 𝓞 p r (v + 1)) (e z)
    exact ⟨x, by rw [hρ_apply, hx, AddEquiv.symm_apply_apply]⟩
  have hρker : ∀ x, ρ x = 0 ↔ ∃ y, x = (p : 𝓞) ^ (v + 1) • y := by
    intro x
    rw [hρ_apply, AddEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, mem_P]
  have hρF : ∀ x, ρ (D₁.F x) = DieudonneModule.frobenius (ZMod p) p C (ρ x) := by
    intro x
    rw [hρ_apply, hρ_apply, AddEquiv.symm_apply_eq, heF, AddEquiv.apply_symm_apply, quotDatum_F_mk]
  have hρV : ∀ x, ρ (D₁.V x) = DieudonneModule.verschiebung (ZMod p) p C (ρ x) := by
    intro x
    rw [hρ_apply, hρ_apply, AddEquiv.symm_apply_eq, heV, AddEquiv.apply_symm_apply, quotDatum_V_mk]

  let I : Ideal C := Hopf.torsionIdeal (ZMod p) C (p ^ v)
  let q : C →ₐc[ZMod p] C ⧸ I := quotientBialgHom (ZMod p) I
  have hq : Function.Surjective q := quotientBialgHom_surjective (ZMod p) I
  haveI : Module.Finite (ZMod p) (C ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (ZMod p) I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (ZMod p) I)
  have hCI : IsLocalRing (CartierDual (ZMod p) (C ⧸ I)) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective (ZMod p) C (C ⧸ I) q hq hC

  have hexact_hyp : RingHom.ker (q : C →ₐ[ZMod p] C ⧸ I) =
      Ideal.map (Hopf.nsmulBialgHom (ZMod p) C (p ^ v) : C →ₐ[ZMod p] C)
        (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) C)) := by
    rw [quotientBialgHom_toAlgHom, Hopf.toAlgHom_nsmulBialgHom]
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk I x = 0 ↔ x ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨hMq, hexact⟩ :=
    DieudonneModule.map_surjective_and_exact_map_of_ker_eq_map_ker_counit (ZMod p) p C C hC hC (C ⧸ I)
      (Hopf.nsmulBialgHom (ZMod p) C (p ^ v)) q hq hexact_hyp
  have hkerq : ∀ z, DieudonneModule.map (ZMod p) p q z = 0 ↔ ∃ w, z = p ^ v • w := by
    intro z
    rw [hexact z, Set.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, map_nsmulBialgHom p (p ^ v) w⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, map_nsmulBialgHom p (p ^ v) w⟩

  let ψ : (Fin r → 𝓞) →+ DieudonneModule (ZMod p) p (C ⧸ I) := (DieudonneModule.map (ZMod p) p q).comp ρ
  have hψ_apply : ∀ x, ψ x = DieudonneModule.map (ZMod p) p q (ρ x) := fun x => rfl
  have hψsurj : Function.Surjective ψ := hMq.comp hρsurj
  have hsmul : ∀ (k : ℕ) (y : Fin r → 𝓞), (p : 𝓞) ^ k • y = (p ^ k : ℕ) • y := by
    intro k y
    rw [← Nat.cast_smul_eq_nsmul 𝓞, Nat.cast_pow]
  have hψker : ∀ x, ψ x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y := by
    intro x
    rw [hψ_apply, hkerq]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := hρsurj w
      have h0 : ρ (x - (p : 𝓞) ^ v • y) = 0 := by rw [map_sub, hw, hsmul, map_nsmul, sub_self]
      obtain ⟨y', hy'⟩ := (hρker _).1 h0
      refine ⟨y + (p : 𝓞) • y', ?_⟩
      rw [smul_add, ← mul_smul, ← pow_succ, ← hy', add_sub_cancel]
    · rintro ⟨y, rfl⟩
      exact ⟨ρ y, by rw [hsmul, map_nsmul]⟩
  have hkereq : ψ.ker = S.π.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hψker, S.ker_iff]
  let θ : DieudonneModule (ZMod p) p (C ⧸ I) ≃+ DieudonneModule (ZMod p) p S.B :=
    equivOfSurjective ψ S.π hψsurj S.surj hkereq
  have hθψ : ∀ x, θ (ψ x) = S.π x := equivOfSurjective_apply ψ S.π hψsurj S.surj hkereq
  have hψF : ∀ x, ψ (D₁.F x) = DieudonneModule.frobenius (ZMod p) p (C ⧸ I) (ψ x) := by
    intro x
    rw [hψ_apply, hψ_apply, hρF, DieudonneModule.map_frobenius]
  have hψV : ∀ x, ψ (D₁.V x) = DieudonneModule.verschiebung (ZMod p) p (C ⧸ I) (ψ x) := by
    intro x
    rw [hψ_apply, hψ_apply, hρV, DieudonneModule.map_verschiebung]
  have hθF : ∀ z, θ (DieudonneModule.frobenius (ZMod p) p (C ⧸ I) z) =
      DieudonneModule.frobenius (ZMod p) p S.B (θ z) := by
    intro z
    obtain ⟨x, rfl⟩ := hψsurj z
    rw [← hψF, hθψ, hθψ, S.map_F]
  have hθV : ∀ z, θ (DieudonneModule.verschiebung (ZMod p) p (C ⧸ I) z) =
      DieudonneModule.verschiebung (ZMod p) p S.B (θ z) := by
    intro z
    obtain ⟨x, rfl⟩ := hψsurj z
    rw [← hψV, hθψ, hθψ, S.map_V]

  obtain ⟨g, hgbij, hg⟩ :=
    DieudonneModule.exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual p S.B (C ⧸ I)
      S.unip hCI θ hθF hθV

  have hcardC : Nat.card (DieudonneModule (ZMod p) p C) = p ^ ((v + 1) * r) := by
    rw [Nat.card_congr e.toEquiv, hcardD]
  refine ⟨{
    T := {
      B := C
      unip := hC
      rank := finrank_eq_of_natCard C hC hcardC
      π := ρ
      surj := hρsurj
      ker_iff := hρker
      map_F := hρF
      map_V := hρV }
    s := g.comp q
    surj := hgbij.2.comp hq
    ker := ?_
    compat := ?_ }⟩
  · ext x
    rw [RingHom.mem_ker, BialgHom.comp_apply, map_eq_zero_iff g hgbij.1]
    change Ideal.Quotient.mk I x = 0 ↔ x ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem
  · intro x
    change DieudonneModule.map (ZMod p) p (g.comp q) (ρ x) = S.π x
    rw [DieudonneModule.map_comp, hg, ← hθψ]
    rfl

def next (v : ℕ) (S : Stage p r D₁ v) : Next p r D₁ v S :=
  Classical.choice (nonempty_next hp hker hV v S)

def tower : ∀ v : ℕ, Stage p r D₁ v := fun v =>
  Nat.rec (motive := fun v => Stage p r D₁ v) (Classical.choice (nonempty_stage_zero hker))
    (fun v S => (next hp hker hV v S).T) v

theorem tower_succ (v : ℕ) : tower hp hker hV (v + 1) = (next hp hker hV v (tower hp hker hV v)).T := rfl

end Tower

end DieudonneTowerZMod
p2m_reactivate "P2MW.S_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le.DieudonneTowerZMod"

end
p2m_reactivate "P2MW.S_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le.DieudonneTowerZMod"

open DieudonneTowerZMod in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (r : ℕ) (D₁ : Deformation.DieudonneDatum (p : 𝓞) (Fin r → 𝓞))
    (hV : ∃ N : ℕ, ∀ x, ∃ y, (D₁.V ^ N) x = (p : 𝓞) • y) :
    ∃ (G : ℕ → Type) (_ : ∀ v, CommRing (G v)) (_ : ∀ v, HopfAlgebra (ZMod p) (G v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (G v)) (_ : ∀ v, Module.Finite (ZMod p) (G v))
      (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v),
      (∀ v, Function.Surjective (s v)) ∧ (∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v)) ∧
      (∀ v, IsLocalRing (CartierDual (ZMod p) (G v))) ∧
    ∃ π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v),
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y) ∧
      (∀ v x, π v (D₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x)) ∧
      (∀ v x, π v (D₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x)) ∧
      (∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x) :=
  ⟨fun v => (tower hp hker hV v).B, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance,
    fun v => (next hp hker hV v (tower hp hker hV v)).s,
    fun v => (next hp hker hV v (tower hp hker hV v)).surj,
    fun v => (tower hp hker hV v).rank,
    fun v => (next hp hker hV v (tower hp hker hV v)).ker,
    fun v => (tower hp hker hV v).unip,
    fun v => (tower hp hker hV v).π,
    fun v => (tower hp hker hV v).surj,
    fun v => (tower hp hker hV v).ker_iff,
    fun v => (tower hp hker hV v).map_F,
    fun v => (tower hp hker hV v).map_V,
    fun v => (next hp hker hV v (tower hp hker hV v)).compat⟩

end S_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
end P2MW
export P2MW.S_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le (solution)
