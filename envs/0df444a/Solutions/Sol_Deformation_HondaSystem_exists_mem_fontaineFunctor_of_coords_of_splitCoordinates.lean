-- Prove2me | solution 1 for Deformation.HondaSystem.exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5255916b-23e9-5003-bfc3-9768ffd96674

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Deformation_SplitCoordinates
import Theorems.Thm_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_FontaineLift_isPadicLimit_wPartialSum_adicEval
import Theorems.Thm_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
p2m_attr_erase "instance" "Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply"
p2m_attr_erase "simp" "HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open Function

theorem exists_unique_factor {M D A : Type*} [AddCommGroup M] [AddCommGroup D] [AddCommGroup A]
    (π : M →+ D) (hπ : Surjective π) (η : M →+ A) (hη : ∀ x, π x = 0 → η x = 0) :
    ∃! ηbar : D →+ A, ηbar.comp π = η := by
  classical
  set s := surjInv hπ with hsdef
  have hs : ∀ d, π (s d) = d := surjInv_eq hπ
  have key : ∀ x y, π x = π y → η x = η y := fun x y h => by
    have := hη (x - y) (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨{ toFun := fun d => η (s d), map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · exact (key _ 0 (by rw [hs, map_zero])).trans (map_zero η)
  · intro d d'
    rw [← map_add]
    exact key _ _ (by rw [hs, map_add, hs, hs])
  · ext x
    exact key _ _ (hs (π x))
  · intro η' h'
    ext d
    show η' d = η (s d)
    rw [← h', AddMonoidHom.comp_apply, hs]

theorem exists_factor {M D A : Type*} [AddCommGroup M] [AddCommGroup D] [AddCommGroup A]
    (π : M →+ D) (hπ : Surjective π) (η : M →+ A) (hη : ∀ x, π x = 0 → η x = 0) :
    ∃ ηbar : D →+ A, ∀ x, ηbar (π x) = η x := by
  obtain ⟨ηbar, h, -⟩ := exists_unique_factor π hπ η hη
  exact ⟨ηbar, fun x => DFunLike.congr_fun h x⟩

theorem semiconj_of_factor {M D A : Type*} (π : M → D) (hπ : Surjective π) (ηbar : D → A)
    (FM : M → M) (FD : D → D) (FA : A → A) (hπF : ∀ x, π (FM x) = FD (π x))
    (h : ∀ x, ηbar (π (FM x)) = FA (ηbar (π x))) : ∀ z, ηbar (FD z) = FA (ηbar z) := by
  intro z
  obtain ⟨x, rfl⟩ := hπ z
  rw [← hπF, h]

theorem ker_le_of_pow_smul {𝓞 : Type u} [CommRing 𝓞] {M D A : Type*} [AddCommGroup M] [Module 𝓞 M]
    [AddCommGroup D] [AddCommGroup A] (p : 𝓞) (v : ℕ) (π : M →+ D)
    (hπker : ∀ x, π x = 0 ↔ ∃ y, x = p ^ v • y) (η : M →+ A) (hη : ∀ y : M, η (p ^ v • y) = 0) :
    ∀ x, π x = 0 → η x = 0 := by
  intro x hx
  obtain ⟨y, rfl⟩ := (hπker x).1 hx
  exact hη y

theorem algHom_eq_of_eval_comp_eq (p : ℕ) [Fact p.Prime] {B C S M : Type*} [CommRing B]
    [Bialgebra (ZMod p) B] [CommRing C] [Bialgebra (ZMod p) C] [CommRing S] [Algebra (ZMod p) S]
    [AddCommGroup M]
    (hinj : ∀ f g : B →ₐ[ZMod p] S,
      Deformation.DieudonneModule.eval (ZMod p) p f = Deformation.DieudonneModule.eval (ZMod p) p g →
        f = g)
    (q : B →ₐc[ZMod p] C) (hq : Surjective q)
    (π : M →+ Deformation.DieudonneModule (ZMod p) p B) (hπ : Surjective π)
    (f f' : C →ₐ[ZMod p] S)
    (h : (Deformation.DieudonneModule.eval (ZMod p) p (f.comp (q : B →ₐ[ZMod p] C))).comp π =
      (Deformation.DieudonneModule.eval (ZMod p) p (f'.comp (q : B →ₐ[ZMod p] C))).comp π) :
    f = f' := by
  have h1 : Deformation.DieudonneModule.eval (ZMod p) p (f.comp (q : B →ₐ[ZMod p] C)) =
      Deformation.DieudonneModule.eval (ZMod p) p (f'.comp (q : B →ₐ[ZMod p] C)) := by
    refine AddMonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := hπ z
    exact DFunLike.congr_fun h x
  have h2 := hinj _ _ h1
  refine AlgHom.ext fun c => ?_
  obtain ⟨b, rfl⟩ := hq c
  exact DFunLike.congr_fun h2 b

theorem eval_comp_level_succ (p : ℕ) [Fact p.Prime] {S M : Type*} [CommRing S] [Algebra (ZMod p) S]
    [AddCommGroup M]
    (G Gc : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, Bialgebra (ZMod p) (G v)]
    [∀ v, CommRing (Gc v)] [∀ v, Bialgebra (ZMod p) (Gc v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v)
    (qc : ∀ v, G v →ₐc[ZMod p] Gc v)
    (hqcs : ∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1)))
    (π : ∀ v, M →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (v : ℕ) (f : Gc v →ₐ[ZMod p] S) :
    (Deformation.DieudonneModule.eval (ZMod p) p (f.comp (qc v : G v →ₐ[ZMod p] Gc v))).comp (π v) =
      (Deformation.DieudonneModule.eval (ZMod p) p
        ((f.comp (sc v : Gc (v + 1) →ₐ[ZMod p] Gc v)).comp
          (qc (v + 1) : G (v + 1) →ₐ[ZMod p] Gc (v + 1)))).comp (π (v + 1)) := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← hπs v x,
    ← Deformation.DieudonneModule.eval_comp_bialgHom]

  have key : f.comp ((qc v : G v →ₐ[ZMod p] Gc v).comp (s v : G (v + 1) →ₐ[ZMod p] G v)) =
      f.comp ((sc v : Gc (v + 1) →ₐ[ZMod p] Gc v).comp (qc (v + 1) : G (v + 1) →ₐ[ZMod p] Gc (v + 1))) := by
    have := congrArg (fun φ : G (v + 1) →ₐc[ZMod p] Gc v => f.comp (φ : G (v + 1) →ₐ[ZMod p] Gc v))
      (hqcs v)
    simpa [AlgHom.comp_assoc] using this
  rw [AlgHom.comp_assoc, key, ← AlgHom.comp_assoc]

theorem map_mem_radical_span_natCast {B C : Type*} [CommRing B] [CommRing C] {Φ : Type*} [FunLike Φ B C]
    [RingHomClass Φ B C] (φ : Φ) (p : ℕ) :
    ∀ t ∈ Ideal.span {(p : B)}, φ t ∈ (Ideal.span {(p : C)}).radical := by
  intro t ht
  obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.mp ht
  refine Ideal.le_radical ?_
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem span_natCast_fg {B : Type*} [CommRing B] (p : ℕ) : (Ideal.span {(p : B)}).FG :=
  ⟨{(p : B)}, by simp⟩

theorem divGhost_eq_wPartialSum (p : ℕ) [Fact p.Prime] {ℛ : Type u} [CommRing ℛ] (m : ℕ)
    (X : WittVector p ℛ) :
    WittGhost.divGhost p m X = PLoc.wPartialSum p (fun n => X.coeff (m - n)) (m + 1) := by
  rw [WittGhost.divGhost_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial, map_sum,
    Finset.mul_sum, PLoc.wPartialSum, ← Finset.sum_range_reflect _ (m + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e1 : m + 1 - 1 - j = m - j := by omega
  have e2 : m - (m - j) = j := by omega
  have key : PLoc.invPow p ℛ m * algebraMap ℛ (Localization.Away (p : ℛ)) ((p : ℛ) ^ (m - j)) =
      PLoc.invPow p ℛ j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    rw [Nat.add_sub_cancel_left, PLoc.invPow_add, mul_assoc, PLoc.invPow_mul_algebraMap_pow, mul_one]
  rw [e1, e2, map_mul, ← mul_assoc, key]

theorem wUp_of_truncate_eq_wPartialSum (p : ℕ) [Fact p.Prime] {ℛ : Type u} [CommRing ℛ] (m : ℕ)
    (X : WittVector p ℛ) :
    UnipotentWittCovector.wUp p ℛ (UnipotentWittCovector.of p ℛ (m + 1) (WittVector.truncate (m + 1) X)) =
      PLoc.wPartialSum p (fun n => X.coeff (m - n)) (m + 1) := by
  rw [UnipotentWittCovector.wUp_of_truncate, divGhost_eq_wPartialSum]

section LiftTo

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [Algebra (ZMod p) S]
variable (Gc : ℕ → Type v) [∀ v, CommRing (Gc v)] [∀ v, Bialgebra (ZMod p) (Gc v)]
variable (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v)

def liftTo {v : ℕ} (f : Gc v →ₐ[ZMod p] S) : ∀ w : ℕ, v ≤ w → (Gc w →ₐ[ZMod p] S)
  | 0, h => (Nat.le_zero.mp h) ▸ f
  | w + 1, h =>
    if hv : v = w + 1 then hv ▸ f
    else (liftTo f w (by omega)).comp (sc w : Gc (w + 1) →ₐ[ZMod p] Gc w)

variable {p Gc sc}

theorem liftTo_self {v : ℕ} (f : Gc v →ₐ[ZMod p] S) (h : v ≤ v) : liftTo p Gc sc f v h = f := by
  cases v with
  | zero => rfl
  | succ w =>
    show (if hv : w + 1 = w + 1 then _ else _) = f
    rw [dif_pos rfl]

theorem liftTo_succ {v w : ℕ} (f : Gc v →ₐ[ZMod p] S) (h : v ≤ w) (h' : v ≤ w + 1) :
    liftTo p Gc sc f (w + 1) h' = (liftTo p Gc sc f w h).comp (sc w : Gc (w + 1) →ₐ[ZMod p] Gc w) := by
  show (if hv : v = w + 1 then _ else _) = _
  rw [dif_neg (by omega)]

theorem liftTo_apply_κ {d : ℕ} (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc v)
    (hscκ : ∀ v, (sc v : Gc (v + 1) →ₐ[ZMod p] Gc v).comp (κ (v + 1)) = κ v)
    {v : ℕ} (f : Gc v →ₐ[ZMod p] S) :
    ∀ (w : ℕ) (h : v ≤ w) (F : MvPowerSeries (Fin d) (ZMod p)), liftTo p Gc sc f w h (κ w F) = f (κ v F) := by
  intro w
  induction w with
  | zero =>
    intro h F
    obtain rfl := Nat.le_zero.mp h
    rw [liftTo_self]
  | succ w ih =>
    intro h F
    by_cases hv : v = w + 1
    · subst hv; rw [liftTo_self]
    · rw [liftTo_succ f (by omega) h]
      change liftTo p Gc sc f w _ (((sc w : Gc (w + 1) →ₐ[ZMod p] Gc w).comp (κ (w + 1))) F) = _
      rw [hscκ, ih]

theorem eval_comp_liftTo {M : Type*} [AddCommGroup M]
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, Bialgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (qc : ∀ v, G v →ₐc[ZMod p] Gc v)
    (hqcs : ∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1)))
    (π : ∀ v, M →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    {v : ℕ} (f : Gc v →ₐ[ZMod p] S) :
    ∀ (w : ℕ) (h : v ≤ w),
      (Deformation.DieudonneModule.eval (ZMod p) p
          ((liftTo p Gc sc f w h).comp (qc w : G w →ₐ[ZMod p] Gc w))).comp (π w) =
        (Deformation.DieudonneModule.eval (ZMod p) p (f.comp (qc v : G v →ₐ[ZMod p] Gc v))).comp (π v) := by
  intro w
  induction w with
  | zero =>
    intro h
    obtain rfl := Nat.le_zero.mp h
    rw [liftTo_self]
  | succ w ih =>
    intro h
    by_cases hv : v = w + 1
    · subst hv; rw [liftTo_self]
    · rw [liftTo_succ f (by omega) h, ← eval_comp_level_succ p G Gc s sc qc hqcs π hπs, ih]

end LiftTo

theorem wPartialSum_congr (p : ℕ) {ℛ : Type u} [CommRing ℛ] {a b : ℕ → ℛ} {N : ℕ}
    (h : ∀ k, k < N → a k = b k) : PLoc.wPartialSum p a N = PLoc.wPartialSum p b N := by
  unfold PLoc.wPartialSum
  exact Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

theorem wUp_of_truncate_mk_eq_wPartialSum (p : ℕ) [Fact p.Prime] {ℛ : Type u} [CommRing ℛ] (n : ℕ)
    (c : ℕ → ℛ) :
    UnipotentWittCovector.wUp p ℛ (UnipotentWittCovector.of p ℛ n
      (WittVector.truncate n (WittVector.mk p fun j => c (n - 1 - j)))) = PLoc.wPartialSum p c n := by
  cases n with
  | zero => rw [UnipotentWittCovector.wUp_of_zero, PLoc.wPartialSum_zero]
  | succ m =>
    rw [wUp_of_truncate_eq_wPartialSum]
    refine wPartialSum_congr p fun k hk => ?_
    show c (m + 1 - 1 - (m - k)) = c k
    congr 1
    omega

theorem exists_forall_wSeries_sub_wPartialSum_mem_pSub (p : ℕ) {ℛ : Type u} [CommRing ℛ] (c : ℕ → ℛ)
    (hlim : PLoc.IsPadicLimit p (PLoc.wPartialSum p c) (PLoc.wSeries p c)) :
    ∃ N : ℕ, ∀ n', N ≤ n' → PLoc.wSeries p c - PLoc.wPartialSum p c n' ∈ PLoc.pSub p ℛ := by
  obtain ⟨N, hN⟩ := hlim 1
  refine ⟨N, fun n' hn' => ?_⟩
  rw [← neg_sub]
  exact neg_mem (hN n' hn')

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open MvPowerSeries

section AdicEvalNil

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem isTopologicallyNilpotent_of_mem_radical (J : Ideal S) {a : S} (ha : a ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    IsTopologicallyNilpotent a := by
  letI : TopologicalSpace S := J.adicTopology
  obtain ⟨k, hk⟩ := ha
  show Filter.Tendsto (a ^ ·) Filter.atTop (nhds 0)
  rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
  obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
  rw [pow_add, pow_mul]
  exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))

theorem hasEval_of_mem_radical [Finite σ] (J : Ideal S) {x : σ → S} (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    MvPowerSeries.HasEval x := by
  letI : TopologicalSpace S := J.adicTopology
  refine ⟨fun s => isTopologicallyNilpotent_of_mem_radical J (hx s), ?_⟩
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

theorem hasSum_adicEval [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) (f : MvPowerSeries σ R) :
    letI : TopologicalSpace S := J.adicTopology
    HasSum (fun e : σ →₀ ℕ => algebraMap R S (coeff e f) * e.prod fun s n => x s ^ n)
      (MvFormalGroup.adicEval J x f) := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  exact MvPowerSeries.hasSum_eval₂ continuous_of_discreteTopology (hasEval_of_mem_radical J hx) f

end AdicEvalNil

section AdicEvalMisc

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem isAdicComplete_span_singleton_of_eq_zero {a : S} (ha : a = 0) :
    IsAdicComplete (Ideal.span {a}) S := by
  have h : Ideal.span ({a} : Set S) = ⊥ := Ideal.span_singleton_eq_bot.2 ha
  rw [h]
  exact ⟨⟩

theorem adicEval_map_algebraMap {k : Type*} [CommRing k] [Algebra R k] [Algebra k S]
    [IsScalarTower R k S] {σ : Type*} [Finite σ] (J : Ideal S) [IsAdicComplete J S]
    {x : σ → S} (hx : ∀ s, x s ∈ J.radical) (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval J x (f.map (algebraMap R k)) = MvFormalGroup.adicEval J x f := by
  letI : TopologicalSpace S := J.adicTopology
  letI : WithIdeal S := ⟨J⟩
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  have h1 := hasSum_adicEval (R := k) J hx (f.map (algebraMap R k))
  have h2 := hasSum_adicEval (R := R) J hx f
  have heq : (fun e : σ →₀ ℕ => algebraMap k S (coeff e (f.map (algebraMap R k))) *
      e.prod fun s n => x s ^ n) =
      fun e : σ →₀ ℕ => algebraMap R S (coeff e f) * e.prod fun s n => x s ^ n := by
    funext e
    rw [MvPowerSeries.coeff_map, ← IsScalarTower.algebraMap_apply]
  rw [heq] at h1
  exact h1.unique h2

end AdicEvalMisc

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open Function

theorem exists_int_sub_mem_span_pow {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (V : ℕ) (c : 𝓞) : ∃ N : ℤ, c - (N : 𝓞) ∈ Ideal.span {(p : 𝓞) ^ V} := by
  induction V with
  | zero => exact ⟨0, by simp⟩
  | succ V ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hN
    have hy' : y - ((algebraMap 𝓞 (ZMod p) y).val : 𝓞) ∈ Ideal.span {(p : 𝓞)} := by
      rw [← hker, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hy'
    refine ⟨N + (p : ℤ) ^ V * ((algebraMap 𝓞 (ZMod p) y).val : ℤ),
      Ideal.mem_span_singleton'.mpr ⟨t, ?_⟩⟩
    push_cast
    linear_combination (p : 𝓞) ^ V * ht + hy

theorem map_smul_eq_zsmul_of_sub_mem {𝓞 : Type u} [CommRing 𝓞] {M A : Type*} [AddCommGroup M]
    [Module 𝓞 M] [AddCommGroup A] (p : 𝓞) (V : ℕ) (η : M →+ A) (hη : ∀ y : M, η (p ^ V • y) = 0)
    {c : 𝓞} {N : ℤ} (hN : c - (N : 𝓞) ∈ Ideal.span {p ^ V}) (m : M) : η (c • m) = N • η m := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hN
  have : c • m = p ^ V • (t • m) + (N : 𝓞) • m := by
    rw [smul_smul, ← add_smul, mul_comm, ht, sub_add_cancel]
  rw [this, map_add, hη, zero_add, Int.cast_smul_eq_zsmul, map_zsmul]

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open scoped TensorProduct
open Function

section Tensor

variable {R : Type*} [CommSemiring R] {A B C A' B' : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Semiring A'] [Algebra R A'] [Semiring B'] [Algebra R B'] [CommSemiring C] [Algebra R C]

theorem eq_lift_comp_includeLeft_includeRight (h : A ⊗[R] B →ₐ[R] C) :
    h = Algebra.TensorProduct.lift (h.comp Algebra.TensorProduct.includeLeft)
      (h.comp Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _) := by
  refine AlgHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem eq_and_eq_of_lift_eq_lift {f f' : A →ₐ[R] C} {e e' : B →ₐ[R] C}
    (h : Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.lift f' e' (fun _ _ => Commute.all _ _)) : f = f' ∧ e = e' := by
  constructor
  · refine AlgHom.ext fun a => ?_
    have := DFunLike.congr_fun h (a ⊗ₜ[R] (1 : B))
    rwa [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one,
      mul_one] at this
  · refine AlgHom.ext fun b => ?_
    have := DFunLike.congr_fun h ((1 : A) ⊗ₜ[R] b)
    rwa [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one, one_mul,
      one_mul] at this

theorem lift_map_apply (f : A' →ₐ[R] C) (e : B' →ₐ[R] C) (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') (t : A ⊗[R] B) :
    Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _) (Algebra.TensorProduct.map φ ψ t) =
      Algebra.TensorProduct.lift (f.comp φ) (e.comp ψ) (fun _ _ => Commute.all _ _) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end Tensor

section EvalSplit

variable (p : ℕ) [Fact p.Prime] {G Gc Ge S : Type*} [CommRing G] [Bialgebra (ZMod p) G]
  [CommRing Gc] [Bialgebra (ZMod p) Gc] [CommRing Ge] [Bialgebra (ZMod p) Ge] [CommRing S] [Algebra (ZMod p) S]

theorem lift_comp_eq_convMul (Θ : G →ₐc[ZMod p] Gc ⊗[ZMod p] Ge) (qc : G →ₐc[ZMod p] Gc) (πe : G →ₐc[ZMod p] Ge)
    (hΘ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : G →ₐ[ZMod p] Gc) (πe : G →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b))
    (f : Gc →ₐ[ZMod p] S) (e : Ge →ₐ[ZMod p] S) :
    (Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp (Θ : G →ₐ[ZMod p] Gc ⊗[ZMod p] Ge) =
      (WithConv.toConv (f.comp (qc : G →ₐ[ZMod p] Gc)) * WithConv.toConv (e.comp (πe : G →ₐ[ZMod p] Ge))).ofConv := by
  refine AlgHom.ext fun b => ?_
  change Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _) (Θ b) =
    (WithConv.toConv (f.comp (qc : G →ₐ[ZMod p] Gc)) * WithConv.toConv (e.comp (πe : G →ₐ[ZMod p] Ge))) b
  rw [hΘ b, AlgHom.convMul_apply, lift_map_apply]

theorem eval_lift_comp_eq_add (Θ : G →ₐc[ZMod p] Gc ⊗[ZMod p] Ge) (qc : G →ₐc[ZMod p] Gc) (πe : G →ₐc[ZMod p] Ge)
    (hΘ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : G →ₐ[ZMod p] Gc) (πe : G →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b))
    (f : Gc →ₐ[ZMod p] S) (e : Ge →ₐ[ZMod p] S) :
    Deformation.DieudonneModule.eval (ZMod p) p
        ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp (Θ : G →ₐ[ZMod p] Gc ⊗[ZMod p] Ge)) =
      Deformation.DieudonneModule.eval (ZMod p) p (f.comp (qc : G →ₐ[ZMod p] Gc)) +
        Deformation.DieudonneModule.eval (ZMod p) p (e.comp (πe : G →ₐ[ZMod p] Ge)) := by
  rw [lift_comp_eq_convMul p Θ qc πe hΘ f e]
  exact AddMonoidHom.ext fun z => Deformation.DieudonneModule.eval_convMul _ _ z

end EvalSplit

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open scoped TensorProduct
open Function

section Residue

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  {g : Type*} [CommRing g] [Algebra 𝓞 g]

include hker in

theorem exists_algHom_tmul_eq_mk :
    ∃ Ψ : ZMod p ⊗[𝓞] g →ₐ[𝓞] g ⧸ Ideal.span {(p : g)},
      ∀ r : g, Ψ ((1 : ZMod p) ⊗ₜ[𝓞] r) = Ideal.Quotient.mk _ r := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hle : RingHom.ker (algebraMap 𝓞 (ZMod p)) ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : g)})).comp (algebraMap 𝓞 g)) := by
    intro o ho
    rw [hker] at ho
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ho
    rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  let κ₀ : ZMod p →+* g ⧸ Ideal.span {(p : g)} := (algebraMap 𝓞 (ZMod p)).liftOfSurjective hk ⟨_, hle⟩
  have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 (ZMod p) o) =
      Ideal.Quotient.mk (Ideal.span {(p : g)}) (algebraMap 𝓞 g o) := fun o =>
    (algebraMap 𝓞 (ZMod p)).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
  let κ : ZMod p →ₐ[𝓞] g ⧸ Ideal.span {(p : g)} := { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
  refine ⟨Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : g)})) fun _ _ => Commute.all _ _,
    fun r => ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

variable {p}
variable {Et : Type u} [CommRing Et] [Algebra 𝓞 Et] {Ge : Type*} [CommRing Ge] [Algebra (ZMod p) Ge]

theorem apply_θe_tmul_of_comp_eq (θe : ZMod p ⊗[𝓞] Et →ₐ[ZMod p] Ge) (e : Ge →ₐ[ZMod p] ZMod p ⊗[𝓞] g)
    (y : Et →ₐ[𝓞] g) (h : e.comp θe = Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y)
    (a : ZMod p) (t : Et) : e (θe (a ⊗ₜ[𝓞] t)) = a ⊗ₜ[𝓞] y t := by
  have := DFunLike.congr_fun h (a ⊗ₜ[𝓞] t)
  rwa [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this

theorem comp_eq_map_of_apply_one_tmul (θe : ZMod p ⊗[𝓞] Et →ₐ[ZMod p] Ge) (e : Ge →ₐ[ZMod p] ZMod p ⊗[𝓞] g)
    (y : Et →ₐ[𝓞] g) (h : ∀ t, e (θe ((1 : ZMod p) ⊗ₜ[𝓞] t)) = (1 : ZMod p) ⊗ₜ[𝓞] y t) :
    e.comp θe = Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y := by
  refine AlgHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a t =>
    have ha : a ⊗ₜ[𝓞] t = a • ((1 : ZMod p) ⊗ₜ[𝓞] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ha, map_smul, map_smul, h,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

include hker in

theorem eq_of_map_id_eq [IsAdicComplete (Ideal.span {(p : g)}) g]
    (hbij : Bijective fun f : Et →ₐ[𝓞] g => (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : g)})).comp f)
    {y y' : Et →ₐ[𝓞] g}
    (h : Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y') : y = y' := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hred_ker := SpecialFibre.ker_reduction_eq_span (ℛ := g) hk hker
  refine hbij.1 (AlgHom.ext fun t => ?_)
  change Ideal.Quotient.mk _ (y t) = Ideal.Quotient.mk _ (y' t)
  rw [Ideal.Quotient.eq, ← hred_ker, RingHom.mem_ker, map_sub, sub_eq_zero, SpecialFibre.reduction_apply,
    SpecialFibre.reduction_apply]
  have := DFunLike.congr_fun h ((1 : ZMod p) ⊗ₜ[𝓞] t)
  rwa [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this

include hker in

theorem exists_comp_θe_eq_map [IsAdicComplete (Ideal.span {(p : g)}) g]
    (hbij : Bijective fun f : Et →ₐ[𝓞] g => (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : g)})).comp f)
    (θe : ZMod p ⊗[𝓞] Et →ₐ[ZMod p] Ge) (e : Ge →ₐ[ZMod p] ZMod p ⊗[𝓞] g) :
    ∃ y : Et →ₐ[𝓞] g, e.comp θe = Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hred_surj := SpecialFibre.reduction_surjective (ℛ := g) hk (k := ZMod p)
  have hred_ker := SpecialFibre.ker_reduction_eq_span (ℛ := g) hk hker
  obtain ⟨Ψ, hΨ⟩ := exists_algHom_tmul_eq_mk p hker (g := g)
  let ψ : Et →ₐ[𝓞] ZMod p ⊗[𝓞] g :=
    ((e.comp θe).restrictScalars 𝓞).comp (Algebra.TensorProduct.includeRight : Et →ₐ[𝓞] ZMod p ⊗[𝓞] Et)
  have hψ : ∀ t, ψ t = e (θe ((1 : ZMod p) ⊗ₜ[𝓞] t)) := fun t => rfl
  obtain ⟨y, hy⟩ := hbij.2 (Ψ.comp ψ)
  refine ⟨y, comp_eq_map_of_apply_one_tmul θe e y fun t => ?_⟩
  have hyt : Ideal.Quotient.mk (Ideal.span {(p : g)}) (y t) = Ψ (ψ t) := DFunLike.congr_fun hy t
  obtain ⟨r, hr⟩ := hred_surj (ψ t)
  rw [SpecialFibre.reduction_apply] at hr
  rw [← hr, hΨ, Ideal.Quotient.eq, ← hred_ker, RingHom.mem_ker, map_sub, sub_eq_zero,
    SpecialFibre.reduction_apply, SpecialFibre.reduction_apply] at hyt
  rw [← hψ, ← hr, hyt]

end Residue

section LiftToR

variable {R : Type*} [CommSemiring R] {T : Type*} [Semiring T] [Algebra R T]
variable (E : ℕ → Type*) [∀ v, Semiring (E v)] [∀ v, Algebra R (E v)]
variable (t : ∀ v, E (v + 1) →ₐ[R] E v)

def liftToR {v : ℕ} (y : E v →ₐ[R] T) : ∀ w : ℕ, v ≤ w → (E w →ₐ[R] T)
  | 0, h => (Nat.le_zero.mp h) ▸ y
  | w + 1, h =>
    if hv : v = w + 1 then hv ▸ y
    else (liftToR y w (by omega)).comp (t w)

variable {E t}

theorem liftToR_self {v : ℕ} (y : E v →ₐ[R] T) (h : v ≤ v) : liftToR E t y v h = y := by
  cases v with
  | zero => rfl
  | succ w =>
    show (if hv : w + 1 = w + 1 then _ else _) = y
    rw [dif_pos rfl]

theorem liftToR_succ {v w : ℕ} (y : E v →ₐ[R] T) (h : v ≤ w) (h' : v ≤ w + 1) :
    liftToR E t y (w + 1) h' = (liftToR E t y w h).comp (t w) := by
  show (if hv : v = w + 1 then _ else _) = _
  rw [dif_neg (by omega)]

theorem liftToR_apply_of_compat (c : ∀ v, E v) (hc : ∀ v, t v (c (v + 1)) = c v) {v : ℕ} (y : E v →ₐ[R] T) :
    ∀ (w : ℕ) (h : v ≤ w), liftToR E t y w h (c w) = y (c v) := by
  intro w
  induction w with
  | zero =>
    intro h
    obtain rfl := Nat.le_zero.mp h
    rw [liftToR_self]
  | succ w ih =>
    intro h
    by_cases hv : v = w + 1
    · subst hv; rw [liftToR_self]
    · rw [liftToR_succ y (by omega) h, AlgHom.comp_apply, hc, ih]

end LiftToR

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open scoped TensorProduct
open Function

theorem algHom_eq_of_eval_comp_eq' (p : ℕ) [Fact p.Prime] {B S M : Type*} [CommRing B]
    [Bialgebra (ZMod p) B] [CommRing S] [Algebra (ZMod p) S] [AddCommGroup M]
    (hinj : ∀ f g : B →ₐ[ZMod p] S,
      Deformation.DieudonneModule.eval (ZMod p) p f = Deformation.DieudonneModule.eval (ZMod p) p g → f = g)
    (π : M →+ Deformation.DieudonneModule (ZMod p) p B) (hπ : Surjective π) (h h' : B →ₐ[ZMod p] S)
    (he : (Deformation.DieudonneModule.eval (ZMod p) p h).comp π =
      (Deformation.DieudonneModule.eval (ZMod p) p h').comp π) : h = h' := by
  refine hinj _ _ (AddMonoidHom.ext fun z => ?_)
  obtain ⟨x, rfl⟩ := hπ z
  exact DFunLike.congr_fun he x

section ThetaTransport

variable (p : ℕ) [Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞] [Algebra 𝓞 (ZMod p)]
variable {S : Type*} [CommRing S] [Algebra (ZMod p) S]
variable (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, Bialgebra (ZMod p) (Ge v)]
variable (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
variable (Et : ℕ → Type u) [∀ v, CommRing (Et v)] [∀ v, Algebra 𝓞 (Et v)]
variable (st : ∀ v, Et (v + 1) →ₐ[𝓞] Et v)
variable {g : Type*} [CommRing g] [Algebra 𝓞 g] [Algebra (ZMod p) (ZMod p ⊗[𝓞] g)]

theorem liftTo_apply_θe_tmul (θe : ∀ v, ZMod p ⊗[𝓞] Et v →ₐ[ZMod p] Ge v)
    (hθe : ∀ v (a : ZMod p) (t : Et (v + 1)), θe v (a ⊗ₜ[𝓞] st v t) = se v (θe (v + 1) (a ⊗ₜ[𝓞] t)))
    {v : ℕ} (e : Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] g) (y : Et v →ₐ[𝓞] g)
    (h : ∀ (a : ZMod p) (t : Et v), e (θe v (a ⊗ₜ[𝓞] t)) = a ⊗ₜ[𝓞] y t) :
    ∀ (w : ℕ) (hw : v ≤ w) (a : ZMod p) (t : Et w),
      Deformation.HondaSystem.CMixed2.liftTo p Ge se e w hw (θe w (a ⊗ₜ[𝓞] t)) =
        a ⊗ₜ[𝓞] Deformation.HondaSystem.CMixed2.liftToR Et st y w hw t := by
  intro w
  induction w with
  | zero =>
    intro hw a t
    obtain rfl := Nat.le_zero.mp hw
    rw [liftTo_self, liftToR_self, h]
  | succ w ih =>
    intro hw a t
    by_cases hv : v = w + 1
    · subst hv; rw [liftTo_self, liftToR_self, h]
    · rw [liftTo_succ e (by omega) hw, liftToR_succ y (by omega) hw, AlgHom.comp_apply, AlgHom.comp_apply]
      change liftTo p Ge se e w _ (se w (θe (w + 1) (a ⊗ₜ[𝓞] t))) = _
      rw [← hθe, ih]

end ThetaTransport

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

p2m_open "Deformation P2MW.S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates.Deformation Deformation.PLoc"

theorem exists_forall_wSeries_sub_wPartialSum_mem_pSub_of_forall_mem (p : ℕ) [Fact p.Prime]
    {g : Type u} [CommRing g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (c : ℕ → g) (n : ℕ) (hc : ∀ k, n ≤ k → c k ∈ Ideal.span {(p : g)}) :
    ∃ N : ℕ, ∀ n', N ≤ n' → wSeries p c - wPartialSum p c n' ∈ pSub p g := by
  obtain ⟨N, hN⟩ := Deformation.PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span p g c ⟨n, hc⟩ 1
  refine ⟨N, fun n' hn' => ?_⟩
  rw [← neg_sub]
  exact neg_mem (hN n' hn')

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

p2m_open "Deformation P2MW.S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates.Deformation"

theorem exists_covector_lift (p : ℕ) [Fact p.Prime] {g : Type u} [CommRing g] {S : Type*} [CommRing S]
    (red : g →+* S) {B : Type*} [CommRing B] (f : B →+* S) {n : ℕ} (u : TruncatedWittVector p n B)
    (c : ℕ → g) (hc_lt : ∀ (k : ℕ) (hk : k < n), red (c k) = f (u.coeff ⟨n - 1 - k, by omega⟩))
    (hc_ge : ∀ k, n ≤ k → red (c k) = 0) (N : ℕ) :
    ∃ Z : UnipotentWittCovector p g,
      UnipotentWittCovector.map p red Z = UnipotentWittCovector.of p S n (TruncWitt.map f u) ∧
      UnipotentWittCovector.wUp p g Z = PLoc.wPartialSum p c (n + N) := by
  set n' := n + N with hn'
  set Xw : WittVector p g := WittVector.mk p fun j => c (n' - 1 - j) with hXw
  refine ⟨UnipotentWittCovector.of p g n' (WittVector.truncate n' Xw), ?_,
    wUp_of_truncate_mk_eq_wPartialSum p n' c⟩
  have hle : n ≤ n' := Nat.le_add_right n N
  rw [UnipotentWittCovector.map_of, TruncWitt.map_truncate, ← UnipotentWittCovector.of_shiftLE hle]
  congr 1
  refine TruncatedWittVector.ext fun i => ?_
  rw [WittVector.coeff_truncate, WittVector.map_coeff, TruncWitt.coeff_shiftLE]
  split_ifs with hi
  · rw [TruncWitt.coeff_map]
    have hk : n' - 1 - (i : ℕ) < n := by omega
    rw [show Xw.coeff i = c (n' - 1 - i) from rfl, hc_lt _ hk]
    congr 2
    exact Fin.ext (by simp only; omega)
  · exact hc_ge _ (by omega)

theorem fst_sub_add_wSeries_mem_pSub (p : ℕ) [Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞]
    {M : Type*} [AddCommGroup M] [Module 𝓞 M] (H : HondaSystem (p : 𝓞) M)
    {g : Type*} [CommRing g] [Algebra 𝓞 g] {S : Type*} [CommRing S] [Algebra (ZMod p) S]
    (red : g →+* S) (hred : RingHom.ker red ≤ Ideal.span {(p : g)})
    {z : (H.L →ₗ[𝓞] Localization.Away (p : g)) × (M →+ UnipotentWittCovector p S)}
    (hz : z ∈ HondaSystem.fontaineFunctor p H (ZMod p) red) (l : H.L)
    {B : Type*} [CommRing B] (f : B →+* S) {n : ℕ} (u : TruncatedWittVector p n B)
    {B' : Type*} [CommRing B'] (f' : B' →+* S) {n' : ℕ} (u' : TruncatedWittVector p n' B')
    (hu : z.2 l = UnipotentWittCovector.of p S n (TruncWitt.map f u) +
      UnipotentWittCovector.of p S n' (TruncWitt.map f' u'))
    (c : ℕ → g) (hc_lt : ∀ (k : ℕ) (hk : k < n), red (c k) = f (u.coeff ⟨n - 1 - k, by omega⟩))
    (hc_ge : ∀ k, n ≤ k → red (c k) = 0)
    (c' : ℕ → g) (hc'_lt : ∀ (k : ℕ) (hk : k < n'), red (c' k) = f' (u'.coeff ⟨n' - 1 - k, by omega⟩))
    (hc'_ge : ∀ k, n' ≤ k → red (c' k) = 0)
    {N : ℕ} (htail : ∀ m, N ≤ m → PLoc.wSeries p c - PLoc.wPartialSum p c m ∈ PLoc.pSub p g)
    {N' : ℕ} (htail' : ∀ m, N' ≤ m → PLoc.wSeries p c' - PLoc.wPartialSum p c' m ∈ PLoc.pSub p g) :
    z.1 l - (PLoc.wSeries p c + PLoc.wSeries p c') ∈ PLoc.pSub p g := by
  obtain ⟨Z, hZ1, hZ2⟩ := exists_covector_lift p red f u c hc_lt hc_ge N
  obtain ⟨Z', hZ'1, hZ'2⟩ := exists_covector_lift p red f' u' c' hc'_lt hc'_ge N'
  have hZred : UnipotentWittCovector.map p red (Z + Z') = z.2 l := by rw [map_add, hZ1, hZ'1, hu]
  have h1 := HondaSystem.fst_sub_wUp_mem_pSub hred hz l hZred
  have h3 := htail (n + N) (Nat.le_add_left N n)
  have h3' := htail' (n' + N') (Nat.le_add_left N' n')
  have : z.1 l - (PLoc.wSeries p c + PLoc.wSeries p c') =
      (z.1 l - UnipotentWittCovector.wUp p g (Z + Z')) - (PLoc.wSeries p c - PLoc.wPartialSum p c (n + N))
        - (PLoc.wSeries p c' - PLoc.wPartialSum p c' (n' + N')) := by
    rw [map_add, hZ2, hZ'2]; abel
  rw [this]
  exact sub_mem (sub_mem h1 h3) h3'

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open Function
open scoped TensorProduct

section LiftClause

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]

omit hp in

theorem exists_forall_pow_smul_mem_pSub {g : Type*} [CommRing g] [Algebra 𝓞 g]
    (z : Localization.Away (p : g)) :
    ∃ m : ℕ, ∀ V, m ≤ V → ((p : 𝓞) ^ V) • z ∈ PLoc.pSub p g := by
  obtain ⟨k, a, rfl⟩ := PLoc.exists_eq_invPow_mul_algebraMap p z
  refine ⟨k + 1, fun V hV => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hV
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝓞 g (Localization.Away (p : g)), map_pow,
    map_natCast, show ((p : g) : g) ^ (k + 1 + e) = (p : g) ^ k * ((p : g) ^ (1 + e)) by rw [← pow_add, add_assoc],
    map_mul, mul_assoc, mul_left_comm _ (PLoc.invPow p g k), ← mul_assoc,
    PLoc.algebraMap_pow_mul_invPow, one_mul, ← map_mul, pow_add, pow_one, mul_assoc]
  exact PLoc.algebraMap_mul_mem_pSub p _

theorem exists_lift_of_basis [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {M : Type*} [AddCommGroup M] [Module 𝓞 M] (L : Submodule 𝓞 M)
    {ι : Type*} [Fintype ι] (α : Module.Basis ι 𝓞 L)
    {g : Type*} [CommRing g] [Algebra 𝓞 g] {S : Type*} [CommRing S] (red : g →+* S)
    (ξ : L →ₗ[𝓞] Localization.Away (p : g)) (η : M →+ UnipotentWittCovector p S)
    (V : ℕ) (hηV : ∀ y : M, η ((p : 𝓞) ^ V • y) = 0)
    (hden : ∀ i, ((p : 𝓞) ^ V) • ξ (α i) ∈ PLoc.pSub p g)
    (Z : ι → UnipotentWittCovector p g)
    (hZ : ∀ i, UnipotentWittCovector.map p red (Z i) = η (α i : L))
    (hw : ∀ i, ξ (α i) - UnipotentWittCovector.wUp p g (Z i) ∈ PLoc.pSub p g) (l : L) :
    ∃ Zl : UnipotentWittCovector p g, UnipotentWittCovector.map p red Zl = η (l : M) ∧
      (Submodule.Quotient.mk (ξ l) : Localization.Away (p : g) ⧸ PLoc.pSub p g) =
        Submodule.Quotient.mk (UnipotentWittCovector.wUp p g Zl) := by
  classical
  choose N hN using fun i => exists_int_sub_mem_span_pow p hker V (α.repr l i)
  refine ⟨∑ i, N i • Z i, ?_, ?_⟩
  · rw [map_sum]
    conv_rhs => rw [← α.sum_repr l, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hZ, Submodule.coe_smul, map_smul_eq_zsmul_of_sub_mem ((p : 𝓞)) V η hηV (hN i)]
  · have hl : ξ l = ∑ i, ξ (α.repr l i • α i) := by
      conv_lhs => rw [← α.sum_repr l]
      rw [map_sum]
    rw [Submodule.Quotient.eq, map_sum, hl, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hN i)
    have e : ξ (α.repr l i • α i) - UnipotentWittCovector.wUp p g (N i • Z i) =
        t • (((p : 𝓞) ^ V) • ξ (α i)) +
          ((N i : ℤ) : 𝓞) • (ξ (α i) - UnipotentWittCovector.wUp p g (Z i)) := by
      rw [map_smul, map_zsmul, ← Int.cast_smul_eq_zsmul 𝓞 (N i), smul_sub, smul_smul, ht, sub_smul]
      abel
    rw [e]
    exact add_mem (Submodule.smul_of_tower_mem _ t (hden i))
      (Submodule.smul_of_tower_mem _ ((N i : ℤ) : 𝓞) (hw i))

end LiftClause

section Thm2Free

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_lift_of_realisation {g S : Type*} [CommRing g] [CommRing S] (red : g →+* S)
    {n : ℕ} (w : TruncatedWittVector p n S) (c : ℕ → g)
    (hc_lt : ∀ (k : ℕ) (hk : k < n), red (c k) = w.coeff ⟨n - 1 - k, by omega⟩)
    (hc_ge : ∀ k, n ≤ k → red (c k) = 0) (N : ℕ) :
    ∃ Z : UnipotentWittCovector p g,
      UnipotentWittCovector.map p red Z = UnipotentWittCovector.of p S n w ∧
      UnipotentWittCovector.wUp p g Z = PLoc.wPartialSum p c (n + N) := by
  refine ⟨UnipotentWittCovector.of p g (n + N)
      (WittVector.truncate (n + N) (WittVector.mk p fun j => c (n + N - 1 - j))), ?_,
    wUp_of_truncate_mk_eq_wPartialSum p (n + N) c⟩
  rw [UnipotentWittCovector.map_of, ← UnipotentWittCovector.of_shiftLE (Nat.le_add_right n N) w]
  congr 1
  refine TruncatedWittVector.ext fun j => ?_
  rw [TruncWitt.coeff_map, WittVector.coeff_truncate, WittVector.coeff_mk, TruncWitt.coeff_shiftLE]
  split_ifs with hj
  · have hk : n + N - 1 - (j : ℕ) < n := by have := j.2; omega
    rw [hc_lt _ hk]
    congr 1
    exact Fin.ext (by simp only []; have := j.2; omega)
  · exact hc_ge _ (by have := j.2; omega)

theorem includeRight_mem_radical {𝓞 : Type*} [CommRing 𝓞] [Algebra 𝓞 (ZMod p)]
    {g : Type*} [CommRing g] [Algebra 𝓞 g] {y : g} (hy : y ∈ (Ideal.span {(p : g)}).radical) :
    (Algebra.TensorProduct.includeRight (R := 𝓞) (A := ZMod p) y : ZMod p ⊗[𝓞] g) ∈
      (Ideal.span {(p : ZMod p ⊗[𝓞] g)}).radical := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨k, ?_⟩
  rw [← map_pow, ← ht, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

theorem isNilpotent_includeRight {𝓞 : Type*} [CommRing 𝓞] [Algebra 𝓞 (ZMod p)]
    {g : Type*} [CommRing g] [Algebra 𝓞 g] {y : g} (hy : y ∈ (Ideal.span {(p : g)}).radical) :
    IsNilpotent (Algebra.TensorProduct.includeRight (R := 𝓞) (A := ZMod p) y : ZMod p ⊗[𝓞] g) := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨k, ?_⟩
  rw [← map_pow, ← ht, map_mul, map_natCast,
    show ((p : ℕ) : ZMod p ⊗[𝓞] g) = 0 by
      rw [← map_natCast (algebraMap (ZMod p) (ZMod p ⊗[𝓞] g)), ZMod.natCast_self, map_zero],
    mul_zero]

theorem natCast_tensor_eq_zero {𝓞 : Type*} [CommRing 𝓞] [Algebra 𝓞 (ZMod p)]
    (g : Type*) [CommRing g] [Algebra 𝓞 g] : ((p : ℕ) : ZMod p ⊗[𝓞] g) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (ZMod p ⊗[𝓞] g)), ZMod.natCast_self, map_zero]

theorem includeRight_adicEval {𝓞 : Type*} [CommRing 𝓞] [Algebra 𝓞 (ZMod p)] {d : ℕ}
    {g : Type*} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    [IsAdicComplete (Ideal.span {(p : ZMod p ⊗[𝓞] g)}) (ZMod p ⊗[𝓞] g)]
    (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical) (F : MvPowerSeries (Fin d) 𝓞) :
    (Algebra.TensorProduct.includeRight (R := 𝓞) (A := ZMod p)
        (MvFormalGroup.adicEval (Ideal.span {(p : g)}) x F) : ZMod p ⊗[𝓞] g) =
      MvFormalGroup.adicEval (Ideal.span {(p : ZMod p ⊗[𝓞] g)})
        (fun j => (1 : ZMod p) ⊗ₜ[𝓞] x j) (F.map (algebraMap 𝓞 (ZMod p))) := by
  have hx' : ∀ j, ((1 : ZMod p) ⊗ₜ[𝓞] x j : ZMod p ⊗[𝓞] g) ∈
      (Ideal.span {(p : ZMod p ⊗[𝓞] g)}).radical := fun j => includeRight_mem_radical p (hx j)
  rw [adicEval_map_algebraMap (R := 𝓞) (k := ZMod p) _ hx' F]
  exact MvFormalGroup.map_adicEval (Ideal.span {(p : g)}) (Ideal.span {(p : ZMod p ⊗[𝓞] g)})
    (Algebra.TensorProduct.includeRight (R := 𝓞) (A := ZMod p)) ⟨{(p : g)}, by simp⟩
    (fun s hs => Ideal.le_radical (by
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))) hx F

end Thm2Free

end Deformation.HondaSystem.CMixed2

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_verschiebung DieudonneModule.eval_frobenius DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.algebraMap_pow_mul_invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.algebraMap_mul_mem_pSub PLoc.exists_eq_invPow_mul_algebraMap PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace CMixed2
p2m_open "Deformation.HondaSystem Deformation"

open scoped TensorProduct
p2m_open "Function MvPowerSeries Deformation P2MW.S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates.Deformation"

theorem apply_κ_eq_and_apply_ĉ_eq_of_eval_comp_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Surjective (π v))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful)
    (g : Type u) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]

    (hinj : ∀ (w : ℕ) (h h' : G w →ₐ[ZMod p] ZMod p ⊗[𝓞] g),
      Deformation.DieudonneModule.eval (ZMod p) p h = Deformation.DieudonneModule.eval (ZMod p) p h' → h = h')
    (η : (Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (ZMod p ⊗[𝓞] g))
    {v : ℕ} (f : 𝒮.Gc v →ₐ[ZMod p] ZMod p ⊗[𝓞] g) (e : 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] g)
    (y : 𝒮.Et v →ₐ[𝓞] g)
    (hη : η = (Deformation.DieudonneModule.eval (ZMod p) p
      ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
        (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v))).comp (π v))
    (hy : e.comp (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v) =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y)
    {v' : ℕ} (f' : 𝒮.Gc v' →ₐ[ZMod p] ZMod p ⊗[𝓞] g) (e' : 𝒮.Ge v' →ₐ[ZMod p] ZMod p ⊗[𝓞] g)
    (y' : 𝒮.Et v' →ₐ[𝓞] g)
    (hη' : η = (Deformation.DieudonneModule.eval (ZMod p) p
      ((Algebra.TensorProduct.lift f' e' (fun _ _ => Commute.all _ _)).comp
        (𝒮.Θ v' : G v' →ₐ[ZMod p] 𝒮.Gc v' ⊗[ZMod p] 𝒮.Ge v'))).comp (π v'))
    (hy' : e'.comp (𝒮.θe v' : ZMod p ⊗[𝓞] 𝒮.Et v' →ₐ[ZMod p] 𝒮.Ge v') =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y') :
    (∀ F, f (𝒮.κ v F) = f' (𝒮.κ v' F)) ∧ (∀ i k, y (𝒮.ĉ i k v) = y' (𝒮.ĉ i k v')) := by

  set S := ZMod p ⊗[𝓞] g
  set w := v + v' with hw
  have h1 : v ≤ w := Nat.le_add_right _ _
  have h2 : v' ≤ w := Nat.le_add_left _ _
  set st' : ∀ u, 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u := fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u) with hst'
  have hsc : ∀ u, (𝒮.sc u : 𝒮.Gc (u + 1) →ₐ[ZMod p] 𝒮.Gc u).comp (𝒮.κ (u + 1)) = 𝒮.κ u := hℒ.sc_comp_κ
  have hθe : ∀ u (a : ZMod p) (t : 𝒮.Et (u + 1)),
      (𝒮.θe u : ZMod p ⊗[𝓞] 𝒮.Et u →ₐ[ZMod p] 𝒮.Ge u) (a ⊗ₜ[𝓞] st' u t) =
        𝒮.se u ((𝒮.θe (u + 1) : ZMod p ⊗[𝓞] 𝒮.Et (u + 1) →ₐ[ZMod p] 𝒮.Ge (u + 1)) (a ⊗ₜ[𝓞] t)) :=
    fun u a t => DFunLike.congr_fun (hℒ.θe_comp u) (a ⊗ₜ[𝓞] t)
  have hĉ : ∀ i k u, st' u (𝒮.ĉ i k (u + 1)) = 𝒮.ĉ i k u := hℒ.st_ĉ

  have pair : ∀ {u : ℕ} (fu : 𝒮.Gc u →ₐ[ZMod p] S) (eu : 𝒮.Ge u →ₐ[ZMod p] S) (w : ℕ) (hu : u ≤ w),
      (Deformation.DieudonneModule.eval (ZMod p) p
        ((Algebra.TensorProduct.lift (liftTo p 𝒮.Gc 𝒮.sc fu w hu) (liftTo p 𝒮.Ge 𝒮.se eu w hu)
            (fun _ _ => Commute.all _ _)).comp (𝒮.Θ w : G w →ₐ[ZMod p] 𝒮.Gc w ⊗[ZMod p] 𝒮.Ge w))).comp (π w) =
      (Deformation.DieudonneModule.eval (ZMod p) p
        ((Algebra.TensorProduct.lift fu eu (fun _ _ => Commute.all _ _)).comp
          (𝒮.Θ u : G u →ₐ[ZMod p] 𝒮.Gc u ⊗[ZMod p] 𝒮.Ge u))).comp (π u) := by
    intro u fu eu w hu
    rw [eval_lift_comp_eq_add p (𝒮.Θ w) (𝒮.qc w) (𝒮.πe w) (hℒ.Θ_apply w),
      eval_lift_comp_eq_add p (𝒮.Θ u) (𝒮.qc u) (𝒮.πe u) (hℒ.Θ_apply u),
      AddMonoidHom.add_comp, AddMonoidHom.add_comp,
      eval_comp_liftTo G s 𝒮.qc hℒ.qc_comp_s π hπs fu w hu,
      eval_comp_liftTo G s 𝒮.πe hℒ.πe_comp_s π hπs eu w hu]

  have hpair := (pair f e w h1).trans (hη.symm.trans (hη'.trans (pair f' e' w h2).symm))
  have heq := algHom_eq_of_eval_comp_eq' p (hinj w) (π w) (hπ w) _ _ hpair
  have hlift : Algebra.TensorProduct.lift (liftTo p 𝒮.Gc 𝒮.sc f w h1) (liftTo p 𝒮.Ge 𝒮.se e w h1)
        (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.lift (liftTo p 𝒮.Gc 𝒮.sc f' w h2) (liftTo p 𝒮.Ge 𝒮.se e' w h2)
        (fun _ _ => Commute.all _ _) := by
    refine AlgHom.ext fun t => ?_
    obtain ⟨b, rfl⟩ := (hℒ.Θ_bijective w).2 t
    exact DFunLike.congr_fun heq b
  obtain ⟨hf, he⟩ := eq_and_eq_of_lift_eq_lift hlift
  refine ⟨fun F => ?_, fun i k => ?_⟩
  · rw [← liftTo_apply_κ 𝒮.κ hsc f w h1 F, ← liftTo_apply_κ 𝒮.κ hsc f' w h2 F, hf]
  ·
    have hyw : ∀ (a : ZMod p) (t : 𝒮.Et w), liftTo p 𝒮.Ge 𝒮.se e w h1
        ((𝒮.θe w : ZMod p ⊗[𝓞] 𝒮.Et w →ₐ[ZMod p] 𝒮.Ge w) (a ⊗ₜ[𝓞] t)) =
          a ⊗ₜ[𝓞] liftToR 𝒮.Et st' y w h1 t :=
      liftTo_apply_θe_tmul p 𝒮.Ge 𝒮.se 𝒮.Et st' (fun u => (𝒮.θe u : ZMod p ⊗[𝓞] 𝒮.Et u →ₐ[ZMod p] 𝒮.Ge u))
        hθe e y (apply_θe_tmul_of_comp_eq _ e y hy) w h1
    have hyw' : ∀ (a : ZMod p) (t : 𝒮.Et w), liftTo p 𝒮.Ge 𝒮.se e' w h2
        ((𝒮.θe w : ZMod p ⊗[𝓞] 𝒮.Et w →ₐ[ZMod p] 𝒮.Ge w) (a ⊗ₜ[𝓞] t)) =
          a ⊗ₜ[𝓞] liftToR 𝒮.Et st' y' w h2 t :=
      liftTo_apply_θe_tmul p 𝒮.Ge 𝒮.se 𝒮.Et st' (fun u => (𝒮.θe u : ZMod p ⊗[𝓞] 𝒮.Et u →ₐ[ZMod p] 𝒮.Ge u))
        hθe e' y' (apply_θe_tmul_of_comp_eq _ e' y' hy') w h2
    have hmap : Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (liftToR 𝒮.Et st' y w h1) =
        Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (liftToR 𝒮.Et st' y' w h2) := by
      rw [← comp_eq_map_of_apply_one_tmul (𝒮.θe w : ZMod p ⊗[𝓞] 𝒮.Et w →ₐ[ZMod p] 𝒮.Ge w) _ _
          (fun t => hyw 1 t),
        ← comp_eq_map_of_apply_one_tmul (𝒮.θe w : ZMod p ⊗[𝓞] 𝒮.Et w →ₐ[ZMod p] 𝒮.Ge w) _ _
          (fun t => hyw' 1 t), he]
    have hyy := eq_of_map_id_eq hker (hℒ.bijective_comp_mk g w) hmap
    rw [← liftToR_apply_of_compat (fun u => 𝒮.ĉ i k u) (hĉ i k) y w h1,
      ← liftToR_apply_of_compat (fun u => 𝒮.ĉ i k u) (hĉ i k) y' w h2, hyy]

end Deformation.HondaSystem.CMixed2

open scoped TensorProduct
open MvPowerSeries _root_.Deformation _root_.P2MW.S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates.Deformation Deformation.HondaSystem.CMixed2 in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful) (hNF : 𝒮.NormalForm)
    (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    [IsAdicComplete (Ideal.span {(p : g)}) g]
    (v₁ : ℕ) (y₁ : 𝒮.Et v₁ →ₐ[𝓞] g)
    (x : Fin 𝒮.d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)

    (hx₁ : ∃ f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g, ∀ i, f (𝒮.κ v₁ (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i) :
    ∃ z : (H₁.L →ₗ[𝓞] Localization.Away (p : g)) ×
      ((Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g)),
      z ∈ Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
      (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom ∧
      (∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, z.2 ((p : 𝓞) ^ v₀ • m) = 0) ∧

      (∃ (f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (e : 𝒮.Ge v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
        z.2 = (Deformation.DieudonneModule.eval (ZMod p) p
                ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
                  (𝒮.Θ v₁ : G v₁ →ₐ[ZMod p] 𝒮.Gc v₁ ⊗[ZMod p] 𝒮.Ge v₁))).comp (π v₁) ∧
        e.comp (𝒮.θe v₁ : ZMod p ⊗[𝓞] 𝒮.Et v₁ →ₐ[ZMod p] 𝒮.Ge v₁) =
          Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₁ ∧
        (∀ i, f (𝒮.κ v₁ (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i)) ∧

      (∀ (v : ℕ) (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
          (e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (y : 𝒮.Et v →ₐ[𝓞] g),

          z.2 = (Deformation.DieudonneModule.eval (ZMod p) p
                  ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
                    (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v))).comp (π v) →

          e.comp (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v) =
            Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y →
          (∀ i, f (𝒮.κ v (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i) ∧
          (∀ i, z.1 (𝒮.α i) =
            Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => y (𝒮.ĉ i k v)))) := by
  classical

  set red : g →+* TensorProduct 𝓞 (ZMod p) g :=
    (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom with hred_def
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hred_ker : RingHom.ker red = Ideal.span {(p : g)} := SpecialFibre.ker_reduction_eq_span hk hker
  have hpS : ((p : ℕ) : TensorProduct 𝓞 (ZMod p) g) = 0 := natCast_tensor_eq_zero p g
  haveI : IsAdicComplete (Ideal.span {(p : TensorProduct 𝓞 (ZMod p) g)}) (TensorProduct 𝓞 (ZMod p) g) :=
    isAdicComplete_span_singleton_of_eq_zero hpS
  haveI hGc : ∀ w, IsAdicComplete (Ideal.span {(p : 𝒮.Gc w)}) (𝒮.Gc w) := fun w =>
    isAdicComplete_span_singleton_of_eq_zero (by
      rw [← map_natCast (algebraMap (ZMod p) (𝒮.Gc w)), ZMod.natCast_self, map_zero])
  haveI := hℒ.isComm_Φ₀
  have hD2inj : ∀ (w : ℕ) (h h' : G w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
      Deformation.DieudonneModule.eval (ZMod p) p h = Deformation.DieudonneModule.eval (ZMod p) p h' → h = h' :=
    fun w => (Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
      p (G w) (hunipG w) (TensorProduct 𝓞 (ZMod p) g)).1
  set xb : Fin 𝒮.d → TensorProduct 𝓞 (ZMod p) g := fun j => (1 : ZMod p) ⊗ₜ[𝓞] x j with hxb
  have hxb_rad : ∀ j, xb j ∈ (Ideal.span {(p : TensorProduct 𝓞 (ZMod p) g)}).radical := fun j =>
    includeRight_mem_radical p (hx j)

  obtain ⟨f₁, hf₁X⟩ := hx₁
  have hf₁κ : ∀ F, f₁ (𝒮.κ v₁ F) =
      MvFormalGroup.adicEval (Ideal.span {(p : TensorProduct 𝓞 (ZMod p) g)}) xb F := fun F => by
    rw [hℒ.κ_eval v₁ F, MvFormalGroup.map_adicEval (Ideal.span {(p : 𝒮.Gc v₁)})
      (Ideal.span {(p : TensorProduct 𝓞 (ZMod p) g)}) f₁ (span_natCast_fg p) (map_mem_radical_span_natCast f₁ p)
      (hℒ.κ_X_mem_radical v₁)]
    congr 1
    exact funext hf₁X
  set θE := AlgEquiv.ofBijective (𝒮.θe v₁ : ZMod p ⊗[𝓞] 𝒮.Et v₁ →ₐ[ZMod p] 𝒮.Ge v₁) (hℒ.θe_bijective v₁)
    with hθE
  set e₁ : 𝒮.Ge v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g :=
    (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₁).comp
      (θE.symm : 𝒮.Ge v₁ →ₐ[ZMod p] ZMod p ⊗[𝓞] 𝒮.Et v₁) with he₁
  have he₁θ : e₁.comp (𝒮.θe v₁ : ZMod p ⊗[𝓞] 𝒮.Et v₁ →ₐ[ZMod p] 𝒮.Ge v₁) =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₁ := by
    refine AlgHom.ext fun b => ?_
    show Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₁ (θE.symm (θE b)) = _
    rw [AlgEquiv.symm_apply_apply]
  have hy1 : ∀ t, red (y₁ t) = e₁ (𝒮.θe v₁ ((1 : ZMod p) ⊗ₜ[𝓞] t)) := fun t =>
    (apply_θe_tmul_of_comp_eq _ e₁ y₁ he₁θ 1 t).symm

  set η : (Fin r → 𝓞) →+ UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g) :=
    (Deformation.DieudonneModule.eval (ZMod p) p
      ((Algebra.TensorProduct.lift f₁ e₁ (fun _ _ => Commute.all _ _)).comp
        (𝒮.Θ v₁ : G v₁ →ₐ[ZMod p] 𝒮.Gc v₁ ⊗[ZMod p] 𝒮.Ge v₁))).comp (π v₁) with hη
  set c : Fin 𝒮.d → ℕ → g := fun i n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n) with hc
  set c' : Fin 𝒮.d → ℕ → g := fun i k => y₁ (𝒮.ĉ i k v₁) with hc'
  set ξ : H₁.L →ₗ[𝓞] Localization.Away (p : g) :=
    (𝒮.α).constr 𝓞 fun i => PLoc.wSeries p (c i) + PLoc.wSeries p (c' i) with hξ
  have hξα : ∀ i, ξ (𝒮.α i) = PLoc.wSeries p (c i) + PLoc.wSeries p (c' i) := fun i =>
    (𝒮.α).constr_basis 𝓞 _ i
  have hηv : ∀ m : Fin r → 𝓞, η ((p : 𝓞) ^ v₁ • m) = 0 := fun m => by
    rw [hη, AddMonoidHom.comp_apply, (hπker v₁ _).2 ⟨m, rfl⟩, map_zero]
  have hredc : ∀ i k, red (c i k) = f₁ (𝒮.κ v₁ (𝒮.abar i k)) := fun i k => by
    rw [hf₁κ, ← hℒ.a_map]
    exact includeRight_adicEval p x hx (𝒮.a i k)

  have hηapp : ∀ m, η m =
      Deformation.DieudonneModule.eval (ZMod p) p f₁
          (Deformation.DieudonneModule.map (ZMod p) p (𝒮.qc v₁) (π v₁ m)) +
        Deformation.DieudonneModule.eval (ZMod p) p e₁
          (Deformation.DieudonneModule.map (ZMod p) p (𝒮.πe v₁) (π v₁ m)) := fun m => by
    rw [hη, AddMonoidHom.comp_apply, eval_lift_comp_eq_add p (𝒮.Θ v₁) (𝒮.qc v₁) (𝒮.πe v₁) (hℒ.Θ_apply v₁),
      AddMonoidHom.add_apply, Deformation.DieudonneModule.eval_comp_bialgHom,
      Deformation.DieudonneModule.eval_comp_bialgHom]
  refine ⟨(ξ, η), ⟨fun m => ?_, fun m => ?_, ?_⟩, ⟨v₁, hηv⟩, ⟨f₁, e₁, rfl, he₁θ, hf₁X⟩, ?_⟩
  ·
    rw [hη, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hπF, Deformation.DieudonneModule.eval_frobenius]
  ·
    rw [hη, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hπV, Deformation.DieudonneModule.eval_verschiebung]
  ·
    choose mden hmden using fun i => exists_forall_pow_smul_mem_pSub (𝓞 := 𝓞) p (ξ (𝒮.α i))
    have hZ : ∀ i, ∃ Z : UnipotentWittCovector p g,
        UnipotentWittCovector.map p red Z = η ((𝒮.α i : H₁.L) : Fin r → 𝓞) ∧
        ξ (𝒮.α i) - UnipotentWittCovector.wUp p g Z ∈ PLoc.pSub p g := by
      intro i
      obtain ⟨n, u, hu, hcoef, hzero⟩ := hℒ.realisation_conn v₁ i
      obtain ⟨n', u', hu', hcoef', hzero'⟩ := hℒ.realisation_etale v₁ i
      obtain ⟨N₀, hN₀⟩ := (Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval p (𝒮.a i)
        (hℒ.constantCoeff_a i) g x hx) 1
      have hc'mem : ∀ k, n' ≤ k → c' i k ∈ Ideal.span {(p : g)} := fun k hk => by
        rw [← hred_ker, RingHom.mem_ker, hc']
        show red (y₁ (𝒮.ĉ i k v₁)) = 0
        rw [hy1, hzero' k hk, map_zero]
      obtain ⟨N₀', hN₀'⟩ := exists_forall_wSeries_sub_wPartialSum_mem_pSub_of_forall_mem p (c' i) n' hc'mem
      obtain ⟨Zc, hZc1, hZc2⟩ := exists_covector_lift p red f₁.toRingHom
        (u : TruncatedWittVector p n (𝒮.Gc v₁)) (c i)
        (fun k hk => by rw [hredc, hcoef k hk]; rfl) (fun k hk => by rw [hredc, hzero k hk, map_zero]) N₀
      obtain ⟨Ze, hZe1, hZe2⟩ := exists_covector_lift p red e₁.toRingHom
        (u' : TruncatedWittVector p n' (𝒮.Ge v₁)) (c' i)
        (fun k hk => by
          show red (y₁ (𝒮.ĉ i k v₁)) = e₁ _
          rw [hy1, hcoef' k hk])
        (fun k hk => by
          show red (y₁ (𝒮.ĉ i k v₁)) = 0
          rw [hy1, hzero' k hk, map_zero]) N₀'
      refine ⟨Zc + Ze, ?_, ?_⟩
      · rw [map_add, hZc1, hZe1, hηapp, ← hu, ← hu', Deformation.DieudonneModule.eval_of,
          Deformation.DieudonneModule.eval_of]
      · rw [map_add, hZc2, hZe2, hξα,
          show PLoc.wSeries p (c i) + PLoc.wSeries p (c' i) -
              (PLoc.wPartialSum p (c i) (n + N₀) + PLoc.wPartialSum p (c' i) (n' + N₀')) =
            -(PLoc.wPartialSum p (c i) (n + N₀) - PLoc.wSeries p (c i)) +
              (PLoc.wSeries p (c' i) - PLoc.wPartialSum p (c' i) (n' + N₀')) by abel]
        exact add_mem ((PLoc.pSub p g).neg_mem (hN₀ (n + N₀) (Nat.le_add_left _ _)))
          (hN₀' (n' + N₀') (Nat.le_add_left _ _))
    choose Z hZ1 hZ2 using hZ
    intro l
    refine exists_lift_of_basis p hker H₁.L 𝒮.α red ξ η (v₁ + Finset.univ.sup mden)
      (fun y => ?_) (fun i => hmden i _ ?_) Z hZ1 hZ2 l
    · rw [pow_add, mul_smul]
      exact hηv _
    · exact (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_left _ _)
  ·
    intro v f e y hηfe hye
    obtain ⟨hF, hC⟩ := apply_κ_eq_and_apply_ĉ_eq_of_eval_comp_eq p hker r H₁ G s π hπ hπs 𝒮 hℒ g hD2inj
      η f e y hηfe hye f₁ e₁ y₁ rfl he₁θ
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [hF, hf₁X]
    · change ξ (𝒮.α i) = _
      rw [hξα, show (fun k => y (𝒮.ĉ i k v)) = c' i from funext (hC i)]

end S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_mem_fontaineFunctor_of_coords_of_splitCoordinates (solution)
