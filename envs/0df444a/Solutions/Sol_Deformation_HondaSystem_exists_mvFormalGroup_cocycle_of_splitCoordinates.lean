-- Prove2me | solution 1 for Deformation.HondaSystem.exists_mvFormalGroup_cocycle_of_splitCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fecff81f-b11d-5e9c-8b70-19c2b4fcbd92

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
import Theorems.Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical
import Theorems.Thm_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_HondaSystem_SplitCoordinates_map_mem_fontaineFunctor_and_described
import Theorems.Thm_Deformation_HondaSystem_SplitCoordinates_map_eq_phi0_of_forall_exists_convMul_apply_kappa_X
import Theorems.Thm_MvFormalGroup_exists_algHom_apply_eq_of_isNilpotent_of_ker_eq_span_nthSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_mvFormalGroup_cocycle_of_splitCoordinates
p2m_attr_erase "instance" "Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply"
p2m_attr_erase "simp" "HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

noncomputable section

namespace Deformation
p2m_export "Deformation" "HondaSystem DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.map DieudonneModule.eval DieudonneModule.eval_convMul DieudonneModule.eval_convOne DieudonneModule.eval_comp_bialgHom PLoc.mapLinear PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero HondaSystem.fontaineFunctor HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual HondaSystem.SplitCoordinates.map_mem_fontaineFunctor_and_described HondaSystem.SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor SplitCoordinates SplitCoordinates.map_mem_fontaineFunctor_and_described SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X"
namespace MixedLaw
p2m_open "Deformation.HondaSystem Deformation"

section PClass

variable {A : Type*} [CommRing A] (p : ℕ)

theorem mem_pow_smul_top_iff {x : A} {n : ℕ} :
    x ∈ (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A) ↔ ∃ y, x = (p : A) ^ n * y := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton']
  exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy, mul_comm]⟩⟩

variable {B : Type*} [CommRing B] [Algebra A B] {ι : Type*} (e : B ≃ₗ[A] (ι → A))

variable (A) in
theorem natCast_pow_mul_eq_smul (n : ℕ) (y : B) : (p : B) ^ n * y = ((p : A) ^ n) • y := by
  rw [Algebra.smul_def, map_pow, map_natCast]

include e in
theorem mem_pow_smul_top_iff_coord {x : B} {n : ℕ} :
    x ∈ (Ideal.span {(p : B)}) ^ n • (⊤ : Submodule B B) ↔
      ∀ i, e x i ∈ (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A) := by
  rw [mem_pow_smul_top_iff]
  simp only [mem_pow_smul_top_iff]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨e y i, by rw [natCast_pow_mul_eq_smul A, map_smul, Pi.smul_apply, smul_eq_mul]⟩
  · intro h
    choose c hc using h
    refine ⟨e.symm c, ?_⟩
    apply e.injective
    rw [natCast_pow_mul_eq_smul A, map_smul, e.apply_symm_apply]
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hc i]

include e in
theorem mem_nonZeroDivisors_of_equiv (hp : (p : A) ∈ nonZeroDivisors A) :
    (p : B) ∈ nonZeroDivisors B := by
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
  have hx' : (p : A) • x = 0 := by
    rw [Algebra.smul_def, map_natCast, mul_comm]
    exact hx
  apply e.injective
  rw [map_zero]
  funext i
  have hi : (p : A) * e x i = 0 := by
    rw [← smul_eq_mul, ← Pi.smul_apply, ← map_smul, hx', map_zero, Pi.zero_apply]
  exact mem_nonZeroDivisors_iff_right.1 hp _ (by rw [mul_comm]; exact hi)

include e in
theorem isAdicComplete_of_equiv [IsAdicComplete (Ideal.span {(p : A)}) A] :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hH : IsHausdorff (Ideal.span {(p : B)}) B := by
    refine ⟨fun x hx => ?_⟩
    apply e.injective
    rw [map_zero]
    funext i
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : A)}) A) _ fun n => ?_
    rw [SModEq.zero]
    exact (mem_pow_smul_top_iff_coord p e).1 (SModEq.zero.1 (hx n)) i
  have hP : IsPrecomplete (Ideal.span {(p : B)}) B := by
    refine ⟨fun {f} hf => ?_⟩
    have hcoord : ∀ i, ∃ L : A, ∀ n, e (f n) i ≡ L [SMOD (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A)] := by
      intro i
      refine IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) fun {m n} hmn => ?_
      rw [SModEq.sub_mem, ← Pi.sub_apply, ← map_sub]
      exact (mem_pow_smul_top_iff_coord p e).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hcoord
    refine ⟨e.symm L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_smul_top_iff_coord p e]
    intro i
    rw [map_sub, e.apply_symm_apply, Pi.sub_apply]
    exact SModEq.sub_mem.1 (hL i n)
  exact @IsAdicComplete.mk _ _ _ _ _ _ hH hP

end PClass

section Free

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)

theorem nzd_of_free (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (g : Type*) [CommRing g] [Algebra 𝓞 g]
    [Module.Free 𝓞 g] [Module.Finite 𝓞 g] : (p : g) ∈ nonZeroDivisors g :=
  mem_nonZeroDivisors_of_equiv p (Module.Free.chooseBasis 𝓞 g).equivFun hp

variable (𝓞) in
theorem isAdicComplete_of_free [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (g : Type*) [CommRing g] [Algebra 𝓞 g]
    [Module.Free 𝓞 g] [Module.Finite 𝓞 g] : IsAdicComplete (Ideal.span {(p : g)}) g :=
  isAdicComplete_of_equiv p (Module.Free.chooseBasis 𝓞 g).equivFun

theorem map_mem_radical {S S' : Type*} [CommRing S] [CommRing S'] {F : Type*} [FunLike F S S']
    [RingHomClass F S S'] (φ : F) {x : S} (hs : x ∈ (Ideal.span {(p : S)}).radical) :
    φ x ∈ (Ideal.span {(p : S')}).radical := by
  obtain ⟨n, hn⟩ := hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, Ideal.mem_span_singleton'.2 ⟨φ t, ?_⟩⟩
  rw [← map_pow, ← ht, map_mul, map_natCast]

end Free

section CMixedCore

open Function

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

theorem algHom_eq_of_apply_κ_X_eq (p : ℕ) [Fact p.Prime] {d : ℕ} {B S : Type*} [CommRing B]
    [Algebra (ZMod p) B] [IsAdicComplete (Ideal.span {(p : B)}) B]
    [CommRing S] [Algebra (ZMod p) S] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (κ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] B) (hκ : Surjective κ)
    (hκX : ∀ i, κ (MvPowerSeries.X i) ∈ (Ideal.span {(p : B)}).radical)
    (hκeval : ∀ F, κ F = MvFormalGroup.adicEval (Ideal.span {(p : B)}) (fun i => κ (MvPowerSeries.X i)) F)
    (f f' : B →ₐ[ZMod p] S) (h : ∀ i, f (κ (MvPowerSeries.X i)) = f' (κ (MvPowerSeries.X i))) :
    f = f' := by
  have hfg : (Ideal.span {(p : B)}).FG := ⟨{(p : B)}, by simp⟩
  have hrad : ∀ (φ : B →ₐ[ZMod p] S), ∀ s ∈ Ideal.span {(p : B)}, φ s ∈ (Ideal.span {(p : S)}).radical := by
    intro φ s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    refine Ideal.le_radical ?_
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine AlgHom.ext fun b => ?_
  obtain ⟨F, rfl⟩ := hκ b
  rw [hκeval, MvFormalGroup.map_adicEval _ _ f hfg (hrad f) hκX,
    MvFormalGroup.map_adicEval _ _ f' hfg (hrad f') hκX]
  simp_rw [h]

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
      liftTo p Ge se e w hw (θe w (a ⊗ₜ[𝓞] t)) =
        a ⊗ₜ[𝓞] liftToR Et st y w hw t := by
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

end CMixedCore

section Points

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)]
  {r : ℕ} (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (𝒮 : SplitCoordinates p r H₁ G s π)

abbrev Elt (g : Type u) [CommRing g] [Algebra 𝓞 g] : Type _ :=
  (H₁.L →ₗ[𝓞] Localization.Away (p : g)) ×
    ((Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g))

abbrev Fun (g : Type u) [CommRing g] [Algebra 𝓞 g] : AddSubgroup (Elt p H₁ g) :=
  Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
    (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom

variable {H₁}

def Cont {g : Type u} [CommRing g] [Algebra 𝓞 g] (z : Elt p H₁ g) : Prop :=
  ∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, z.2 ((p : 𝓞) ^ v₀ • m) = 0

variable {p}

theorem Cont.add {g : Type u} [CommRing g] [Algebra 𝓞 g] {z z' : Elt p H₁ g} (hz : Cont p z) (hz' : Cont p z') :
    Cont p (z + z') := by
  obtain ⟨v, hv⟩ := hz
  obtain ⟨v', hv'⟩ := hz'
  refine ⟨v + v', fun m => ?_⟩
  have h1 : z.2 ((p : 𝓞) ^ (v + v') • m) = 0 := by rw [pow_add, mul_smul]; exact hv _
  have h2 : z'.2 ((p : 𝓞) ^ (v + v') • m) = 0 := by rw [pow_add, mul_comm, mul_smul]; exact hv' _
  rw [Prod.snd_add, AddMonoidHom.add_apply, h1, h2, add_zero]

theorem Cont.zero {g : Type u} [CommRing g] [Algebra 𝓞 g] : Cont p (0 : Elt p H₁ g) := ⟨0, fun _ => rfl⟩

variable (p)

def IsPt {g : Type u} [CommRing g] [Algebra 𝓞 g] (z : Elt p H₁ g) (v : ℕ)
    (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) :
    Prop :=
  z.2 = (Deformation.DieudonneModule.eval (ZMod p) p
    ((Algebra.TensorProduct.lift f e (fun _ _ => Commute.all _ _)).comp
      (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v))).comp (π v)

def IsEt {g : Type u} [CommRing g] [Algebra 𝓞 g] (v : ℕ) (e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
    (y : 𝒮.Et v →ₐ[𝓞] g) : Prop :=
  e.comp (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v) =
    Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y

def Coords {g : Type u} [CommRing g] [Algebra 𝓞 g] (v : ℕ) (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
    (x : Fin 𝒮.d → g) : Prop :=
  ∀ i, f (𝒮.κ v (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i

def LogCl {g : Type u} [CommRing g] [Algebra 𝓞 g] (z : Elt p H₁ g) (v : ℕ) (x : Fin 𝒮.d → g)
    (y : 𝒮.Et v →ₐ[𝓞] g) : Prop :=
  ∀ i, z.1 (𝒮.α i) =
    Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
    Deformation.PLoc.wSeries p (fun k => y (𝒮.ĉ i k v))

def Clauses {g : Type u} [CommRing g] [Algebra 𝓞 g] (z : Elt p H₁ g) (x : Fin 𝒮.d → g) : Prop :=
  ∀ (v : ℕ) (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
    (e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (y : 𝒮.Et v →ₐ[𝓞] g),
    IsPt p 𝒮 z v f e → IsEt p 𝒮 v e y → Coords p 𝒮 v f x ∧ LogCl p 𝒮 z v x y

def IsRad {g : Type u} [CommRing g] (x : Fin 𝒮.d → g) : Prop := ∀ j, x j ∈ (Ideal.span {(p : g)}).radical

def HREP : Prop :=
  ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g → IsAdicComplete (Ideal.span {(p : g)}) g →
    ∀ z : Elt p H₁ g, z ∈ Fun p H₁ g → Cont p z → ∃! x : Fin 𝒮.d → g, IsRad p 𝒮 x ∧ Clauses p 𝒮 z x

def HREP' : Prop :=
  ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g → IsAdicComplete (Ideal.span {(p : g)}) g →
    ∀ (v₁ : ℕ) (y₁ : 𝒮.Et v₁ →ₐ[𝓞] g) (x : Fin 𝒮.d → g), IsRad p 𝒮 x →
    (∃ f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g, Coords p 𝒮 v₁ f x) →
    ∃ z : Elt p H₁ g, z ∈ Fun p H₁ g ∧ Cont p z ∧
      (∃ (f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g) (e : 𝒮.Ge v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
        IsPt p 𝒮 z v₁ f e ∧ IsEt p 𝒮 v₁ e y₁ ∧ Coords p 𝒮 v₁ f x) ∧
      Clauses p 𝒮 z x

def unitEt (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) : 𝒮.Et v →ₐ[𝓞] g :=
  (Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))

def unitGe (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g :=
  (Algebra.ofId (ZMod p) _).comp (Bialgebra.counitAlgHom (ZMod p) (𝒮.Ge v))

def unitGc (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g :=
  (Algebra.ofId (ZMod p) _).comp (Bialgebra.counitAlgHom (ZMod p) (𝒮.Gc v))

theorem isEt_unit (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    IsEt p 𝒮 v (unitGe p 𝒮 g v) (unitEt p 𝒮 g v) := by
  refine comp_eq_map_of_apply_one_tmul _ _ _ fun t => ?_
  show algebraMap (ZMod p) (TensorProduct 𝓞 (ZMod p) g)
      (Coalgebra.counit (R := ZMod p) ((𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐc[ZMod p] 𝒮.Ge v) ((1 : ZMod p) ⊗ₜ[𝓞] t))) =
    (1 : ZMod p) ⊗ₜ[𝓞] algebraMap 𝓞 g (Coalgebra.counit (R := 𝓞) t)
  rw [CoalgHomClass.counit_comp_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def,
    mul_one, ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']

end Points

section Constructions

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)]
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (𝒮 : SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful)

include hℒ in

theorem exists_coords (g : Type u) [CommRing g] [Algebra 𝓞 g] (x : Fin 𝒮.d → g) (hx : IsRad p 𝒮 x) :
    ∃ (v : ℕ) (f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g), Coords p 𝒮 v f x := by
  haveI := hℒ.isComm_Φ₀
  refine MvFormalGroup.exists_algHom_apply_eq_of_isNilpotent_of_ker_eq_span_nthSeries p 𝒮.Φ₀ 𝒮.κ hℒ.κ_surjective
    hℒ.ker_κ (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x i) fun i => ?_
  obtain ⟨e, he⟩ := hx i
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 he
  refine ⟨e, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc,
    show c * (p : g) = (p : 𝓞) • c by rw [Algebra.smul_def, map_natCast, mul_comm],
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, map_natCast,
    ZMod.natCast_self, TensorProduct.zero_tmul]

include hℒ in
theorem coords_liftTo {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ}
    {f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {x : Fin 𝒮.d → g} (h : Coords p 𝒮 v f x)
    (w : ℕ) (hw : v ≤ w) : Coords p 𝒮 w (liftTo p 𝒮.Gc 𝒮.sc f w hw) x := fun i => by
  rw [liftTo_apply_κ 𝒮.κ hℒ.sc_comp_κ]
  exact h i

def lvl (g : Type u) [CommRing g] [Algebra 𝓞 g] (x : Fin 𝒮.d → g) (hx : IsRad p 𝒮 x) : ℕ :=
  (exists_coords p 𝒮 hℒ g x hx).choose

def tpt (g : Type u) [CommRing g] [Algebra 𝓞 g] (x : Fin 𝒮.d → g) (hx : IsRad p 𝒮 x) :
    𝒮.Gc (lvl p 𝒮 hℒ g x hx) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g :=
  (exists_coords p 𝒮 hℒ g x hx).choose_spec.choose

theorem coords_tpt (g : Type u) [CommRing g] [Algebra 𝓞 g] (x : Fin 𝒮.d → g) (hx : IsRad p 𝒮 x) :
    Coords p 𝒮 (lvl p 𝒮 hℒ g x hx) (tpt p 𝒮 hℒ g x hx) x :=
  (exists_coords p 𝒮 hℒ g x hx).choose_spec.choose_spec

abbrev raiseEt {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) (w : ℕ) (hw : v ≤ w) :
    𝒮.Et w →ₐ[𝓞] g :=
  liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) y w hw

variable (hREP : HREP p 𝒮) (hREP' : HREP' p 𝒮)

def Θpt (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) (x : Fin 𝒮.d → g)
    (hx : IsRad p 𝒮 x) : Elt p H₁ g :=
  (hREP' g hpg hcg (max v (lvl p 𝒮 hℒ g x hx)) (raiseEt p 𝒮 y _ (le_max_left _ _)) x hx
    ⟨liftTo p 𝒮.Gc 𝒮.sc (tpt p 𝒮 hℒ g x hx) _ (le_max_right _ _),
      coords_liftTo p 𝒮 hℒ (coords_tpt p 𝒮 hℒ g x hx) _ _⟩).choose

section ΘptSpec

variable {g : Type u} [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
  (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) (x : Fin 𝒮.d → g)
  (hx : IsRad p 𝒮 x)

theorem Θpt_mem : Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx ∈ Fun p H₁ g :=
  (hREP' g hpg hcg (max v (lvl p 𝒮 hℒ g x hx)) (raiseEt p 𝒮 y _ (le_max_left _ _)) x hx
    ⟨liftTo p 𝒮.Gc 𝒮.sc (tpt p 𝒮 hℒ g x hx) _ (le_max_right _ _),
      coords_liftTo p 𝒮 hℒ (coords_tpt p 𝒮 hℒ g x hx) _ _⟩).choose_spec.1

theorem Θpt_cont : Cont p (Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx) :=
  (hREP' g hpg hcg (max v (lvl p 𝒮 hℒ g x hx)) (raiseEt p 𝒮 y _ (le_max_left _ _)) x hx
    ⟨liftTo p 𝒮.Gc 𝒮.sc (tpt p 𝒮 hℒ g x hx) _ (le_max_right _ _),
      coords_liftTo p 𝒮 hℒ (coords_tpt p 𝒮 hℒ g x hx) _ _⟩).choose_spec.2.1

theorem Θpt_descr : ∃ (f : 𝒮.Gc (max v (lvl p 𝒮 hℒ g x hx)) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
    (e : 𝒮.Ge (max v (lvl p 𝒮 hℒ g x hx)) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
    IsPt p 𝒮 (Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx) _ f e ∧ IsEt p 𝒮 _ e (raiseEt p 𝒮 y _ (le_max_left _ _)) ∧
    Coords p 𝒮 _ f x :=
  (hREP' g hpg hcg (max v (lvl p 𝒮 hℒ g x hx)) (raiseEt p 𝒮 y _ (le_max_left _ _)) x hx
    ⟨liftTo p 𝒮.Gc 𝒮.sc (tpt p 𝒮 hℒ g x hx) _ (le_max_right _ _),
      coords_liftTo p 𝒮 hℒ (coords_tpt p 𝒮 hℒ g x hx) _ _⟩).choose_spec.2.2.1

theorem Θpt_clauses : Clauses p 𝒮 (Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx) x :=
  (hREP' g hpg hcg (max v (lvl p 𝒮 hℒ g x hx)) (raiseEt p 𝒮 y _ (le_max_left _ _)) x hx
    ⟨liftTo p 𝒮.Gc 𝒮.sc (tpt p 𝒮 hℒ g x hx) _ (le_max_right _ _),
      coords_liftTo p 𝒮 hℒ (coords_tpt p 𝒮 hℒ g x hx) _ _⟩).choose_spec.2.2.2

end ΘptSpec

def Θinv (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) (z : Elt p H₁ g) (hz : z ∈ Fun p H₁ g) (hzc : Cont p z) :
    Fin 𝒮.d → g :=
  (hREP g hpg hcg z hz hzc).exists.choose

section ΘinvSpec

variable {g : Type u} [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
  (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) (z : Elt p H₁ g) (hz : z ∈ Fun p H₁ g) (hzc : Cont p z)

theorem Θinv_rad : IsRad p 𝒮 (Θinv p 𝒮 hREP g hpg hcg z hz hzc) := (hREP g hpg hcg z hz hzc).exists.choose_spec.1

theorem Θinv_clauses : Clauses p 𝒮 z (Θinv p 𝒮 hREP g hpg hcg z hz hzc) :=
  (hREP g hpg hcg z hz hzc).exists.choose_spec.2

theorem eq_Θinv {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hcl : Clauses p 𝒮 z x) :
    x = Θinv p 𝒮 hREP g hpg hcg z hz hzc :=
  (hREP g hpg hcg z hz hzc).unique ⟨hx, hcl⟩ ⟨Θinv_rad p 𝒮 hREP hpg hcg z hz hzc, Θinv_clauses p 𝒮 hREP hpg hcg z hz hzc⟩

theorem Θinv_congr {z' : Elt p H₁ g} (hz' : z' ∈ Fun p H₁ g) (hzc' : Cont p z') (h : z = z') :
    Θinv p 𝒮 hREP g hpg hcg z hz hzc = Θinv p 𝒮 hREP g hpg hcg z' hz' hzc' := by
  subst h; rfl

end ΘinvSpec

end Constructions

section PairCalculus

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)]
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (𝒮 : SplitCoordinates p r H₁ G s π)

theorem span_natCast_eq_bot (A : Type*) [CommRing A] [Algebra (ZMod p) A] : Ideal.span {(p : A)} = ⊥ := by
  rw [Ideal.span_singleton_eq_bot, ← map_natCast (algebraMap (ZMod p) A), ZMod.natCast_self, map_zero]

theorem isAdicComplete_span_natCast (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  rw [span_natCast_eq_bot p A]; infer_instance

theorem raiseEt_trans {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) (w₁ : ℕ)
    (h₁ : v ≤ w₁) : ∀ (w : ℕ) (h : w₁ ≤ w), raiseEt p 𝒮 (raiseEt p 𝒮 y w₁ h₁) w h = raiseEt p 𝒮 y w (h₁.trans h) := by
  intro w
  induction w with
  | zero =>
    intro h
    obtain rfl := Nat.le_zero.mp h
    exact liftToR_self _ _
  | succ w ih =>
    intro h
    by_cases hw : w₁ = w + 1
    · subst hw
      exact liftToR_self _ _
    · have hv : ¬ v = w + 1 := by omega
      show liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) (raiseEt p 𝒮 y w₁ h₁) (w + 1) h =
        liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) y (w + 1) (h₁.trans h)
      rw [liftToR_succ _ (show w₁ ≤ w by omega) h, liftToR_succ _ (show v ≤ w by omega) (h₁.trans h)]
      exact congrArg (fun φ => AlgHom.comp φ _) (ih (by omega))

theorem raiseEt_unit (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    ∀ (w : ℕ) (h : v ≤ w), raiseEt p 𝒮 (unitEt p 𝒮 g v) w h = unitEt p 𝒮 g w := by
  intro w
  induction w with
  | zero => intro h; obtain rfl := Nat.le_zero.mp h; exact liftToR_self _ _
  | succ w ih =>
    intro h
    by_cases hv : v = w + 1
    · subst hv; exact liftToR_self _ _
    · show liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) (unitEt p 𝒮 g v) (w + 1) h = _
      rw [liftToR_succ _ (show v ≤ w by omega) h]
      change (raiseEt p 𝒮 (unitEt p 𝒮 g v) w _).comp _ = _
      rw [ih (by omega)]
      refine AlgHom.ext fun t => ?_
      show algebraMap 𝓞 g (Coalgebra.counit (R := 𝓞) ((𝒮.st w : 𝒮.Et (w + 1) →ₐc[𝓞] 𝒮.Et w) t)) =
        algebraMap 𝓞 g (Coalgebra.counit (R := 𝓞) t)
      rw [CoalgHomClass.counit_comp_apply]

variable (hℒ : 𝒮.Lawful)
include hℒ

theorem coords_unitGc_zero (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) : Coords p 𝒮 v (unitGc p 𝒮 g v) 0 := by
  intro i
  show algebraMap (ZMod p) _ (Coalgebra.counit (R := ZMod p) (𝒮.κ v (X i))) = _
  rw [hℒ.counit_κ_X, map_zero, Pi.zero_apply, TensorProduct.tmul_zero]

theorem eq_of_coords_eq {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ}
    {f f' : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {x : Fin 𝒮.d → g} (hf : Coords p 𝒮 v f x)
    (hf' : Coords p 𝒮 v f' x) : f = f' := by
  haveI := isAdicComplete_span_natCast p (𝒮.Gc v)
  haveI := isAdicComplete_span_natCast p (TensorProduct 𝓞 (ZMod p) g)
  exact algHom_eq_of_apply_κ_X_eq p (𝒮.κ v) (hℒ.κ_surjective v) (hℒ.κ_X_mem_radical v) (hℒ.κ_eval v) f f'
    fun i => by rw [hf i, hf' i]

theorem eq_of_isEt_eq {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ}
    {e e' : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {y : 𝒮.Et v →ₐ[𝓞] g} (he : IsEt p 𝒮 v e y)
    (he' : IsEt p 𝒮 v e' y) : e = e' := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨t, rfl⟩ := (hℒ.θe_bijective v).2 b
  have := DFunLike.congr_fun (he.trans he'.symm) t
  exact this

theorem isPt_liftTo (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    {g : Type u} [CommRing g] [Algebra 𝓞 g] {z : Elt p H₁ g} {u : ℕ}
    {fu : 𝒮.Gc u →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {eu : 𝒮.Ge u →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    (h : IsPt p 𝒮 z u fu eu) (w : ℕ) (hu : u ≤ w) :
    IsPt p 𝒮 z w (liftTo p 𝒮.Gc 𝒮.sc fu w hu) (liftTo p 𝒮.Ge 𝒮.se eu w hu) := by
  rw [IsPt] at h ⊢
  rw [h, eval_lift_comp_eq_add p (𝒮.Θ w) (𝒮.qc w) (𝒮.πe w) (hℒ.Θ_apply w),
    eval_lift_comp_eq_add p (𝒮.Θ u) (𝒮.qc u) (𝒮.πe u) (hℒ.Θ_apply u),
    AddMonoidHom.add_comp, AddMonoidHom.add_comp,
    eval_comp_liftTo G s 𝒮.qc hℒ.qc_comp_s π hπs fu w hu,
    eval_comp_liftTo G s 𝒮.πe hℒ.πe_comp_s π hπs eu w hu]

theorem isEt_liftTo {g : Type u} [CommRing g] [Algebra 𝓞 g] {u : ℕ}
    {eu : 𝒮.Ge u →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {y : 𝒮.Et u →ₐ[𝓞] g} (h : IsEt p 𝒮 u eu y)
    (w : ℕ) (hu : u ≤ w) : IsEt p 𝒮 w (liftTo p 𝒮.Ge 𝒮.se eu w hu) (raiseEt p 𝒮 y w hu) := by
  refine comp_eq_map_of_apply_one_tmul _ _ _ fun t => ?_
  exact liftTo_apply_θe_tmul p 𝒮.Ge 𝒮.se 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u))
    (fun u => (𝒮.θe u : ZMod p ⊗[𝓞] 𝒮.Et u →ₐ[ZMod p] 𝒮.Ge u))
    (fun u a t => DFunLike.congr_fun (hℒ.θe_comp u) (a ⊗ₜ[𝓞] t)) eu y (apply_θe_tmul_of_comp_eq _ eu y h) w hu 1 t

theorem logCl_raiseEt_iff {g : Type u} [CommRing g] [Algebra 𝓞 g] {z : Elt p H₁ g} {v : ℕ} {y : 𝒮.Et v →ₐ[𝓞] g}
    {x : Fin 𝒮.d → g} (w : ℕ) (hw : v ≤ w) : LogCl p 𝒮 z w x (raiseEt p 𝒮 y w hw) ↔ LogCl p 𝒮 z v x y := by
  have : ∀ i k, raiseEt p 𝒮 y w hw (𝒮.ĉ i k w) = y (𝒮.ĉ i k v) := fun i k =>
    liftToR_apply_of_compat (fun u => 𝒮.ĉ i k u) (hℒ.st_ĉ i k) y w hw
  simp only [LogCl, this]

theorem eq_of_descr (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    {g : Type u} [CommRing g] [Algebra 𝓞 g] {z z' : Elt p H₁ g}
    {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) (x : Fin 𝒮.d → g)
    {w₁ : ℕ} (h₁ : v ≤ w₁) {f₁ : 𝒮.Gc w₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    {e₁ : 𝒮.Ge w₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    (hP₁ : IsPt p 𝒮 z w₁ f₁ e₁) (hE₁ : IsEt p 𝒮 w₁ e₁ (raiseEt p 𝒮 y w₁ h₁)) (hC₁ : Coords p 𝒮 w₁ f₁ x)
    (hL₁ : LogCl p 𝒮 z w₁ x (raiseEt p 𝒮 y w₁ h₁))
    {w₂ : ℕ} (h₂ : v ≤ w₂) {f₂ : 𝒮.Gc w₂ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    {e₂ : 𝒮.Ge w₂ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    (hP₂ : IsPt p 𝒮 z' w₂ f₂ e₂) (hE₂ : IsEt p 𝒮 w₂ e₂ (raiseEt p 𝒮 y w₂ h₂)) (hC₂ : Coords p 𝒮 w₂ f₂ x)
    (hL₂ : LogCl p 𝒮 z' w₂ x (raiseEt p 𝒮 y w₂ h₂)) : z = z' := by
  refine Prod.ext ?_ ?_
  ·
    refine 𝒮.α.ext fun i => ?_
    rw [(logCl_raiseEt_iff p 𝒮 hℒ w₁ h₁).1 hL₁ i, (logCl_raiseEt_iff p 𝒮 hℒ w₂ h₂).1 hL₂ i]
  ·
    set w := w₁ + w₂
    have k₁ : w₁ ≤ w := Nat.le_add_right _ _
    have k₂ : w₂ ≤ w := Nat.le_add_left _ _
    have hP₁' := isPt_liftTo p 𝒮 hℒ hπs hP₁ w k₁
    have hP₂' := isPt_liftTo p 𝒮 hℒ hπs hP₂ w k₂
    have hf : liftTo p 𝒮.Gc 𝒮.sc f₁ w k₁ = liftTo p 𝒮.Gc 𝒮.sc f₂ w k₂ :=
      eq_of_coords_eq p 𝒮 hℒ (coords_liftTo p 𝒮 hℒ hC₁ w k₁) (coords_liftTo p 𝒮 hℒ hC₂ w k₂)
    have he : liftTo p 𝒮.Ge 𝒮.se e₁ w k₁ = liftTo p 𝒮.Ge 𝒮.se e₂ w k₂ := by
      have hE₁' := isEt_liftTo p 𝒮 hℒ hE₁ w k₁
      have hE₂' := isEt_liftTo p 𝒮 hℒ hE₂ w k₂
      rw [raiseEt_trans p 𝒮 y w₁ h₁ w k₁] at hE₁'
      rw [raiseEt_trans p 𝒮 y w₂ h₂ w k₂] at hE₂'
      exact eq_of_isEt_eq p 𝒮 hℒ hE₁' hE₂'
    rw [IsPt] at hP₁' hP₂'
    rw [hP₁', hP₂', hf, he]

end PairCalculus

end Deformation.HondaSystem.MixedLaw

end

noncomputable section

namespace Deformation
p2m_export "Deformation" "HondaSystem DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.map DieudonneModule.eval DieudonneModule.eval_convMul DieudonneModule.eval_convOne DieudonneModule.eval_comp_bialgHom PLoc.mapLinear PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero HondaSystem.fontaineFunctor HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual HondaSystem.SplitCoordinates.map_mem_fontaineFunctor_and_described HondaSystem.SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor SplitCoordinates SplitCoordinates.map_mem_fontaineFunctor_and_described SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X"
namespace MixedLaw
p2m_open "Deformation.HondaSystem Deformation"

section Analytic

open MvPowerSeries.WithPiTopology Filter

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero (x : σ → S) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) (r : MvPolynomial σ R) :
    MvPolynomial.eval₂ (algebraMap R S) x r =
      ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  change ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) = _
  have h1 : ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => by
      rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]
  have h2 : ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => by
      rw [hT m hm, mul_zero]
  rw [h1, h2]

theorem adicEval_eq_aeval_of_forall_prod_eq_zero
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (q : MvPolynomial σ R) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0)
    (hq : ∀ m ∈ T, MvPolynomial.coeff m q = MvPowerSeries.coeff m F) :
    MvFormalGroup.adicEval J x F = MvPolynomial.aeval x q := by
  classical
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : T2Space S := (IsAdic.isHausdorff_iff (show IsAdic J from rfl)).mp hJ

  set c : S := ∑ m ∈ T, algebraMap R S (MvPowerSeries.coeff m F) * m.prod (fun s e => x s ^ e)
    with hc
  have key : ∀ r : MvPolynomial σ R,
      (∀ m ∈ T, MvPolynomial.coeff m r = MvPowerSeries.coeff m F) →
      MvPolynomial.eval₂ (algebraMap R S) x r = c := fun r hr => by
    rw [mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero x T hT r, hc]
    exact Finset.sum_congr rfl fun m hm => by rw [hr m hm]
  rw [MvPolynomial.aeval_def, key q hq]
  change MvPowerSeries.eval₂ (algebraMap R S) x F = c
  unfold MvPowerSeries.eval₂
  split_ifs with H
  · refine key _ fun m _ => ?_
    rw [← MvPolynomial.coeff_coe, H.choose_spec]
  · refine MvPolynomial.toMvPowerSeries_isDenseInducing.extend_eq_of_tendsto ?_
    have hU : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} ∈
        nhds F := by
      have : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} =
          ⋂ m ∈ T, {G : MvPowerSeries σ R | MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} := by
        ext G
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this, Filter.biInter_finset_mem]
      intro m _
      exact ((isOpen_discrete ({MvPowerSeries.coeff m F} : Set R)).preimage
        (continuous_coeff (R := R) m)).mem_nhds rfl
    refine Filter.Tendsto.congr' (Filter.mem_of_superset (Filter.preimage_mem_comap hU)
      fun r hr => ?_) tendsto_const_nhds
    exact (key r fun m hm => by rw [← MvPolynomial.coeff_coe]; exact hr m hm).symm

theorem adicEval_zero_eq (J : Ideal S) (hJ : IsHausdorff J S) (F : MvPowerSeries σ R) :
    MvFormalGroup.adicEval J (0 : σ → S) F = algebraMap R S (MvPowerSeries.constantCoeff F) := by
  classical
  have h := adicEval_eq_aeval_of_forall_prod_eq_zero J hJ (0 : σ → S) F
    (MvPolynomial.C (MvPowerSeries.constantCoeff F)) {0} (fun m hm => ?_) (fun m hm => ?_)
  · rw [h, MvPolynomial.aeval_C]
  · have hm0 : m ≠ 0 := fun h0 => hm (by rw [h0]; exact Finset.mem_singleton_self _)
    obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hm0
    rw [Finsupp.prod]
    exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 ht) (by simp only [Pi.zero_apply]; exact zero_pow ht)
  · rw [Finset.mem_singleton.1 hm, MvPolynomial.coeff_C, if_pos rfl]
    rfl

end Analytic

section Sums

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)]
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (𝒮 : SplitCoordinates p r H₁ G s π)

theorem unitGc_eq_one (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    unitGc p 𝒮 g v = (1 : WithConv (𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)).ofConv :=
  AlgHom.ext fun b => by rw [AlgHom.convOne_apply]; rfl

theorem unitGe_eq_one (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    unitGe p 𝒮 g v = (1 : WithConv (𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)).ofConv :=
  AlgHom.ext fun b => by rw [AlgHom.convOne_apply]; rfl

theorem unitEt_eq_one (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    unitEt p 𝒮 g v = (1 : WithConv (𝒮.Et v →ₐ[𝓞] g)).ofConv :=
  AlgHom.ext fun b => by rw [AlgHom.convOne_apply]; rfl

theorem unitGc_convMul (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ)
    (X : WithConv (𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)) : WithConv.toConv (unitGc p 𝒮 g v) * X = X := by
  rw [unitGc_eq_one, WithConv.toConv_ofConv]; exact one_mul X

theorem convMul_unitGe (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ)
    (X : WithConv (𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)) : X * WithConv.toConv (unitGe p 𝒮 g v) = X := by
  rw [unitGe_eq_one, WithConv.toConv_ofConv]; exact mul_one X

theorem unitGe_convMul (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ)
    (X : WithConv (𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)) : WithConv.toConv (unitGe p 𝒮 g v) * X = X := by
  rw [unitGe_eq_one, WithConv.toConv_ofConv]; exact one_mul X

theorem unitEt_convMul (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) (Y : WithConv (𝒮.Et v →ₐ[𝓞] g)) :
    WithConv.toConv (unitEt p 𝒮 g v) * Y = Y := by
  rw [unitEt_eq_one, WithConv.toConv_ofConv]; exact one_mul Y

theorem convMul_unitEt (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) (Y : WithConv (𝒮.Et v →ₐ[𝓞] g)) :
    Y * WithConv.toConv (unitEt p 𝒮 g v) = Y := by
  rw [unitEt_eq_one, WithConv.toConv_ofConv]; exact mul_one Y

theorem eval_convMul_eq_add {B T : Type*} [CommRing B] [Bialgebra (ZMod p) B] [CommRing T] [Algebra (ZMod p) T]
    (f f' : B →ₐ[ZMod p] T) :
    Deformation.DieudonneModule.eval (ZMod p) p (WithConv.toConv f * WithConv.toConv f').ofConv =
      Deformation.DieudonneModule.eval (ZMod p) p f + Deformation.DieudonneModule.eval (ZMod p) p f' :=
  AddMonoidHom.ext fun z => Deformation.DieudonneModule.eval_convMul _ _ z

theorem eval_unitGc_comp (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    Deformation.DieudonneModule.eval (ZMod p) p ((unitGc p 𝒮 g v).comp (𝒮.qc v : G v →ₐ[ZMod p] 𝒮.Gc v)) = 0 := by
  have : (unitGc p 𝒮 g v).comp (𝒮.qc v : G v →ₐ[ZMod p] 𝒮.Gc v) =
      (1 : WithConv (G v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)).ofConv := by
    refine AlgHom.ext fun b => ?_
    rw [AlgHom.convOne_apply, AlgHom.comp_apply]
    show algebraMap (ZMod p) _ (Coalgebra.counit (R := ZMod p) (𝒮.qc v b)) = _
    rw [CoalgHomClass.counit_comp_apply]
  rw [this]
  exact AddMonoidHom.ext fun z => Deformation.DieudonneModule.eval_convOne z

theorem eval_unitGe_comp (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    Deformation.DieudonneModule.eval (ZMod p) p ((unitGe p 𝒮 g v).comp (𝒮.πe v : G v →ₐ[ZMod p] 𝒮.Ge v)) = 0 := by
  have : (unitGe p 𝒮 g v).comp (𝒮.πe v : G v →ₐ[ZMod p] 𝒮.Ge v) =
      (1 : WithConv (G v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)).ofConv := by
    refine AlgHom.ext fun b => ?_
    rw [AlgHom.convOne_apply, AlgHom.comp_apply]
    show algebraMap (ZMod p) _ (Coalgebra.counit (R := ZMod p) (𝒮.πe v b)) = _
    rw [CoalgHomClass.counit_comp_apply]
  rw [this]
  exact AddMonoidHom.ext fun z => Deformation.DieudonneModule.eval_convOne z

variable (hℒ : 𝒮.Lawful)
include hℒ

theorem isPt_zero (g : Type u) [CommRing g] [Algebra 𝓞 g] (v : ℕ) :
    IsPt p 𝒮 (0 : Elt p H₁ g) v (unitGc p 𝒮 g v) (unitGe p 𝒮 g v) := by
  rw [IsPt, eval_lift_comp_eq_add p (𝒮.Θ v) (𝒮.qc v) (𝒮.πe v) (hℒ.Θ_apply v), eval_unitGc_comp, eval_unitGe_comp,
    add_zero, AddMonoidHom.zero_comp]
  rfl

theorem logCl_zero (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    [IsAdicComplete (Ideal.span {(p : g)}) g] (v : ℕ) : LogCl p 𝒮 (0 : Elt p H₁ g) v 0 (unitEt p 𝒮 g v) := by
  intro i
  have h1 : (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (0 : Fin 𝒮.d → g) (𝒮.a i n)) = fun _ => 0 := by
    funext n
    rw [adicEval_zero_eq _ inferInstance, hℒ.constantCoeff_a, map_zero]
  have h2 : (fun k => unitEt p 𝒮 g v (𝒮.ĉ i k v)) = fun _ => 0 := by
    funext k
    show algebraMap 𝓞 g (Coalgebra.counit (R := 𝓞) (𝒮.ĉ i k v)) = 0
    rw [hℒ.counit_ĉ, map_zero]
  rw [h1, h2, Deformation.PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero p hpg (N := 0) (fun _ _ => rfl),
    Deformation.PLoc.wPartialSum_zero, add_zero]
  rfl

theorem isPt_add {g : Type u} [CommRing g] [Algebra 𝓞 g] {z₁ z₂ : Elt p H₁ g} {w : ℕ}
    {f₁ f₂ : 𝒮.Gc w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {e₁ e₂ : 𝒮.Ge w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    (h₁ : IsPt p 𝒮 z₁ w f₁ e₁) (h₂ : IsPt p 𝒮 z₂ w f₂ e₂) :
    IsPt p 𝒮 (z₁ + z₂) w (WithConv.toConv f₁ * WithConv.toConv f₂).ofConv
      (WithConv.toConv e₁ * WithConv.toConv e₂).ofConv := by
  rw [IsPt] at h₁ h₂ ⊢
  rw [Prod.snd_add, h₁, h₂, ← AddMonoidHom.add_comp,
    eval_lift_comp_eq_add p (𝒮.Θ w) (𝒮.qc w) (𝒮.πe w) (hℒ.Θ_apply w),
    eval_lift_comp_eq_add p (𝒮.Θ w) (𝒮.qc w) (𝒮.πe w) (hℒ.Θ_apply w),
    eval_lift_comp_eq_add p (𝒮.Θ w) (𝒮.qc w) (𝒮.πe w) (hℒ.Θ_apply w),
    AlgHom.convMul_comp_bialgHom_distrib, AlgHom.convMul_comp_bialgHom_distrib,
    eval_convMul_eq_add, eval_convMul_eq_add]
  abel

omit hℒ in

theorem map_id_convMul {g : Type u} [CommRing g] [Algebra 𝓞 g] {w : ℕ} (y₁ y₂ : 𝒮.Et w →ₐ[𝓞] g) :
    (WithConv.toConv (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₁) *
        WithConv.toConv (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y₂)).ofConv =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (WithConv.toConv y₁ * WithConv.toConv y₂).ofConv := by
  apply Algebra.TensorProduct.ext'
  intro a t
  rw [AlgHom.convMul_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.convMul_apply,
    TensorProduct.comul_tmul, CommSemiring.comul_apply]

  generalize Coalgebra.comul (R := 𝓞) t = T
  induction T using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero, TensorProduct.tmul_zero]
  | tmul t₁ t₂ =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, TensorProduct.tmul_add]

omit hℒ in

theorem isEt_mul {g : Type u} [CommRing g] [Algebra 𝓞 g] {w : ℕ}
    {e₁ e₂ : 𝒮.Ge w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {y₁ y₂ : 𝒮.Et w →ₐ[𝓞] g}
    (h₁ : IsEt p 𝒮 w e₁ y₁) (h₂ : IsEt p 𝒮 w e₂ y₂) :
    IsEt p 𝒮 w (WithConv.toConv e₁ * WithConv.toConv e₂).ofConv (WithConv.toConv y₁ * WithConv.toConv y₂).ofConv := by
  rw [IsEt] at h₁ h₂ ⊢
  rw [AlgHom.convMul_comp_bialgHom_distrib, h₁, h₂, map_id_convMul]

end Sums

section Repr

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)]
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
  (𝒮 : SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful) (hREP : HREP p 𝒮) (hREP' : HREP' p 𝒮)
  {g : Type u} [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
  (hcg : IsAdicComplete (Ideal.span {(p : g)}) g)

include hℒ hπs

theorem eq_Θpt {z : Elt p H₁ g} {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x)
    {w : ℕ} (hw : v ≤ w) {f : 𝒮.Gc w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    {e : 𝒮.Ge w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    (hP : IsPt p 𝒮 z w f e) (hE : IsEt p 𝒮 w e (raiseEt p 𝒮 y w hw)) (hC : Coords p 𝒮 w f x)
    (hL : LogCl p 𝒮 z w x (raiseEt p 𝒮 y w hw)) :
    z = Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx := by
  obtain ⟨f', e', hP', hE', hC'⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg y x hx
  have hL' := (Θpt_clauses p 𝒮 hℒ hREP' hpg hcg y x hx _ f' e' _ hP' hE').2
  exact eq_of_descr p 𝒮 hℒ hπs y x hw hP hE hC hL (le_max_left _ _) hP' hE' hC' hL'

theorem Θpt_raiseEt {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (w : ℕ) (hw : v ≤ w) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg (raiseEt p 𝒮 y w hw) x hx = Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx := by
  obtain ⟨f', e', hP', hE', hC'⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg (raiseEt p 𝒮 y w hw) x hx
  have hL' := (Θpt_clauses p 𝒮 hℒ hREP' hpg hcg (raiseEt p 𝒮 y w hw) x hx _ f' e' _ hP' hE').2
  rw [raiseEt_trans p 𝒮 y w hw] at hE' hL'
  exact eq_Θpt p hπs 𝒮 hℒ hREP' hpg hcg y hx _ hP' hE' hC' hL'

theorem Θpt_unit_zero (v : ℕ) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g v) 0 (fun _ => Ideal.zero_mem _) = 0 := by
  haveI := hcg
  symm
  refine eq_Θpt p hπs 𝒮 hℒ hREP' hpg hcg (unitEt p 𝒮 g v) _ le_rfl (isPt_zero p 𝒮 hℒ g v) ?_
    (coords_unitGc_zero p 𝒮 hℒ g v) ?_
  · rw [raiseEt_unit]; exact isEt_unit p 𝒮 g v
  · rw [raiseEt_unit]; exact logCl_zero p 𝒮 hℒ g hpg v

omit hπs in

theorem Θinv_Θpt {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) :
    Θinv p 𝒮 hREP g hpg hcg (Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx) (Θpt_mem p 𝒮 hℒ hREP' hpg hcg y x hx)
      (Θpt_cont p 𝒮 hℒ hREP' hpg hcg y x hx) = x :=
  (eq_Θinv p 𝒮 hREP hpg hcg _ _ _ hx (Θpt_clauses p 𝒮 hℒ hREP' hpg hcg y x hx)).symm

theorem eq_Θpt_Θinv {z : Elt p H₁ g} (hz : z ∈ Fun p H₁ g) (hzc : Cont p z) {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g)
    {w : ℕ} (hw : v ≤ w) {f : 𝒮.Gc w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    {e : 𝒮.Ge w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    (hP : IsPt p 𝒮 z w f e) (hE : IsEt p 𝒮 w e (raiseEt p 𝒮 y w hw)) :
    z = Θpt p 𝒮 hℒ hREP' g hpg hcg y (Θinv p 𝒮 hREP g hpg hcg z hz hzc) (Θinv_rad p 𝒮 hREP hpg hcg z hz hzc) := by
  obtain ⟨hC, hL⟩ := Θinv_clauses p 𝒮 hREP hpg hcg z hz hzc _ f e _ hP hE
  exact eq_Θpt p hπs 𝒮 hℒ hREP' hpg hcg y _ hw hP hE hC hL

theorem Θpt_eq_add {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx =
      Θpt p 𝒮 hℒ hREP' g hpg hcg y 0 (fun _ => Ideal.zero_mem _) +
        Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g v) x hx := by
  haveI := hcg

  obtain ⟨f₁, e₁, hP₁, hE₁, hC₁⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg y (0 : Fin 𝒮.d → g) (fun _ => Ideal.zero_mem _)
  obtain ⟨f₂, e₂, hP₂, hE₂, hC₂⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg (unitEt p 𝒮 g v) x hx
  obtain ⟨w, k₁, k₂⟩ : ∃ w : ℕ, max v (lvl p 𝒮 hℒ g (0 : Fin 𝒮.d → g) (fun _ => Ideal.zero_mem _)) ≤ w ∧
      max v (lvl p 𝒮 hℒ g x hx) ≤ w := ⟨_, Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  have hL₁ := (Θpt_clauses p 𝒮 hℒ hREP' hpg hcg y (0 : Fin 𝒮.d → g) (fun _ => Ideal.zero_mem _) _ f₁ e₁ _ hP₁ hE₁).2
  have hL₂ := (Θpt_clauses p 𝒮 hℒ hREP' hpg hcg (unitEt p 𝒮 g v) x hx _ f₂ e₂ _ hP₂ hE₂).2

  have hP₁' := isPt_liftTo p 𝒮 hℒ hπs hP₁ w k₁
  have hP₂' := isPt_liftTo p 𝒮 hℒ hπs hP₂ w k₂
  have hE₁' := isEt_liftTo p 𝒮 hℒ hE₁ w k₁
  have hE₂' := isEt_liftTo p 𝒮 hℒ hE₂ w k₂
  rw [raiseEt_trans] at hE₁' hE₂'
  rw [raiseEt_unit] at hE₂'
  have hC₁' := coords_liftTo p 𝒮 hℒ hC₁ w k₁
  have hC₂' := coords_liftTo p 𝒮 hℒ hC₂ w k₂

  have hf₁ : liftTo p 𝒮.Gc 𝒮.sc f₁ w k₁ = unitGc p 𝒮 g w := eq_of_coords_eq p 𝒮 hℒ hC₁' (coords_unitGc_zero p 𝒮 hℒ g w)
  have he₂ : liftTo p 𝒮.Ge 𝒮.se e₂ w k₂ = unitGe p 𝒮 g w := eq_of_isEt_eq p 𝒮 hℒ hE₂' (isEt_unit p 𝒮 g w)

  rw [hf₁] at hP₁'
  rw [he₂] at hP₂'
  have hPs := isPt_add p 𝒮 hℒ hP₁' hP₂'
  rw [unitGc_convMul, convMul_unitGe, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at hPs
  symm
  refine eq_Θpt p hπs 𝒮 hℒ hREP' hpg hcg y hx (show v ≤ w from (le_max_left _ _).trans k₁) hPs hE₁' hC₂' ?_

  refine (logCl_raiseEt_iff p 𝒮 hℒ _ ((le_max_left _ _).trans k₁)).2 (fun i => ?_)
  have h1 := (logCl_raiseEt_iff p 𝒮 hℒ _ (le_max_left _ _)).1 hL₁ i
  have h2 := (logCl_raiseEt_iff p 𝒮 hℒ _ (le_max_left _ _)).1 hL₂ i
  have hz1 : (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (0 : Fin 𝒮.d → g) (𝒮.a i n)) = fun _ => 0 := by
    funext n; rw [adicEval_zero_eq _ inferInstance, hℒ.constantCoeff_a, map_zero]
  have hz2 : (fun k => unitEt p 𝒮 g v (𝒮.ĉ i k v)) = fun _ => 0 := by
    funext k
    show algebraMap 𝓞 g (Coalgebra.counit (R := 𝓞) (𝒮.ĉ i k v)) = 0
    rw [hℒ.counit_ĉ, map_zero]
  have hW0 : Deformation.PLoc.wSeries p (fun _ : ℕ => (0 : g)) = 0 := by
    rw [Deformation.PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero p hpg (N := 0) (fun _ _ => rfl),
      Deformation.PLoc.wPartialSum_zero]
  rw [Prod.fst_add, LinearMap.add_apply, h1, h2, hz1, hz2, hW0, zero_add, add_zero, add_comm]

end Repr

section Rigid

open Function

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

end Rigid

section Push

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
  (hπ : ∀ v, Surjective (π v))
  (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
  (𝒮 : SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful)

abbrev Fmap {g g' : Type u} [CommRing g] [Algebra 𝓞 g] [CommRing g'] [Algebra 𝓞 g'] (φ : g →ₐ[𝓞] g') :
    TensorProduct 𝓞 (ZMod p) g →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g' :=
  Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) φ

def push {g g' : Type u} [CommRing g] [Algebra 𝓞 g] [CommRing g'] [Algebra 𝓞 g'] (φ : g →ₐ[𝓞] g')
    (z : Elt p H₁ g) : Elt p H₁ g' :=
  ((Deformation.PLoc.mapLinear p φ).comp z.1,
    (Deformation.UnipotentWittCovector.map p (Fmap p φ).toRingHom).comp z.2)

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
theorem push_add {g g' : Type u} [CommRing g] [Algebra 𝓞 g] [CommRing g'] [Algebra 𝓞 g'] (φ : g →ₐ[𝓞] g')
    (z₁ z₂ : Elt p H₁ g) : push p φ (z₁ + z₂) = push p φ z₁ + push p φ z₂ :=
  Prod.ext (LinearMap.comp_add _ _ _) (AddMonoidHom.comp_add _ _ _)

include hker hℒ in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem push_descr {g g' : Type u} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    [CommRing g'] [Algebra 𝓞 g'] [IsAdicComplete (Ideal.span {(p : g')}) g'] (hpg' : (p : g') ∈ nonZeroDivisors g')
    (φ : g →ₐ[𝓞] g') {z : Elt p H₁ g} (hz : z ∈ Fun p H₁ g) {v : ℕ}
    {f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    {y : 𝒮.Et v →ₐ[𝓞] g} {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hP : IsPt p 𝒮 z v f e) (hE : IsEt p 𝒮 v e y)
    (hC : Coords p 𝒮 v f x) (hL : LogCl p 𝒮 z v x y) :
    push p φ z ∈ Fun p H₁ g' ∧ (Cont p z → Cont p (push p φ z)) ∧
      IsPt p 𝒮 (push p φ z) v ((Fmap p φ).comp f) ((Fmap p φ).comp e) ∧ IsEt p 𝒮 v ((Fmap p φ).comp e) (φ.comp y) ∧
      Coords p 𝒮 v ((Fmap p φ).comp f) (φ ∘ x) ∧ LogCl p 𝒮 (push p φ z) v (φ ∘ x) (φ.comp y) :=
  Deformation.HondaSystem.SplitCoordinates.map_mem_fontaineFunctor_and_described p hker r H₁ G s π 𝒮 hℒ g g' hpg'
    φ z hz v f e y x hx hP hE hC hL

include hker hunipG hπ hπs hℒ in

theorem clauses_push {g g' : Type u} [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    [CommRing g'] [Algebra 𝓞 g'] [IsAdicComplete (Ideal.span {(p : g')}) g'] (hpg' : (p : g') ∈ nonZeroDivisors g')
    (φ : g →ₐ[𝓞] g') {z : Elt p H₁ g} (hz : z ∈ Fun p H₁ g) {v : ℕ}
    {f : 𝒮.Gc v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g} {e : 𝒮.Ge v →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g}
    {y : 𝒮.Et v →ₐ[𝓞] g} {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hP : IsPt p 𝒮 z v f e) (hE : IsEt p 𝒮 v e y)
    (hcl : Clauses p 𝒮 z x) : Clauses p 𝒮 (push p φ z) (φ ∘ x) := by
  intro v' f' e' y' hP' hE'
  obtain ⟨hC, hL⟩ := hcl v f e y hP hE
  obtain ⟨-, -, hPφ, hEφ, hCφ, hLφ⟩ := push_descr p hker 𝒮 hℒ hpg' φ hz hx hP hE hC hL
  have hinj : ∀ (w : ℕ) (h h' : G w →ₐ[ZMod p] ZMod p ⊗[𝓞] g'),
      Deformation.DieudonneModule.eval (ZMod p) p h = Deformation.DieudonneModule.eval (ZMod p) p h' → h = h' :=
    fun w => (Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual p (G w)
      (hunipG w) (ZMod p ⊗[𝓞] g')).1
  obtain ⟨hκ, hĉ⟩ := apply_κ_eq_and_apply_ĉ_eq_of_eval_comp_eq p hker r H₁ G s π hπ hπs 𝒮 hℒ g' hinj
    (push p φ z).2 _ _ _ hPφ hEφ f' e' y' hP' hE'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [← hκ]; exact hCφ i
  · rw [hLφ i]
    congr 1
    exact congrArg _ (funext fun k => hĉ i k)

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem raiseEt_mul {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) :
    ∀ (w : ℕ) (hw : v ≤ w), raiseEt p 𝒮 (WithConv.toConv y₁ * WithConv.toConv y₂).ofConv w hw =
      (WithConv.toConv (raiseEt p 𝒮 y₁ w hw) * WithConv.toConv (raiseEt p 𝒮 y₂ w hw)).ofConv := by
  intro w
  induction w with
  | zero => intro h; obtain rfl := Nat.le_zero.mp h; simp only [raiseEt, liftToR_self]
  | succ w ih =>
    intro h
    by_cases hv : v = w + 1
    · subst hv; simp only [raiseEt, liftToR_self]
    · show liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) _ (w + 1) h = _
      rw [liftToR_succ _ (show v ≤ w by omega) h]
      change (raiseEt p 𝒮 _ w _).comp (𝒮.st w : 𝒮.Et (w + 1) →ₐ[𝓞] 𝒮.Et w) = _
      rw [ih (by omega), AlgHom.convMul_comp_bialgHom_distrib]
      show _ = (WithConv.toConv (liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) y₁ (w + 1) h) *
        WithConv.toConv (liftToR 𝒮.Et (fun u => (𝒮.st u : 𝒮.Et (u + 1) →ₐ[𝓞] 𝒮.Et u)) y₂ (w + 1) h)).ofConv
      rw [liftToR_succ _ (show v ≤ w by omega) h, liftToR_succ _ (show v ≤ w by omega) h]

variable (hREP : HREP p 𝒮) (hREP' : HREP' p 𝒮)

include hℒ hπs in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem exists_descr_add {g : Type u} [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
    (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g)
    {x₁ x₂ : Fin 𝒮.d → g} (hx₁ : IsRad p 𝒮 x₁) (hx₂ : IsRad p 𝒮 x₂) :
    ∃ (w : ℕ) (hw : v ≤ w) (f₁ f₂ : 𝒮.Gc w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g)
      (e : 𝒮.Ge w →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g),
      IsPt p 𝒮 (Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ x₁ hx₁ + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ x₂ hx₂) w
        (WithConv.toConv f₁ * WithConv.toConv f₂).ofConv e ∧
      IsEt p 𝒮 w e (raiseEt p 𝒮 (WithConv.toConv y₁ * WithConv.toConv y₂).ofConv w hw) ∧
      Coords p 𝒮 w f₁ x₁ ∧ Coords p 𝒮 w f₂ x₂ := by
  obtain ⟨f₁, e₁, hP₁, hE₁, hC₁⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg y₁ x₁ hx₁
  obtain ⟨f₂, e₂, hP₂, hE₂, hC₂⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg y₂ x₂ hx₂
  obtain ⟨w, k₁, k₂⟩ : ∃ w : ℕ, max v (lvl p 𝒮 hℒ g x₁ hx₁) ≤ w ∧ max v (lvl p 𝒮 hℒ g x₂ hx₂) ≤ w :=
    ⟨_, Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  have hE₁' := isEt_liftTo p 𝒮 hℒ hE₁ w k₁
  have hE₂' := isEt_liftTo p 𝒮 hℒ hE₂ w k₂
  rw [raiseEt_trans] at hE₁' hE₂'
  refine ⟨w, (le_max_left _ _).trans k₁, _, _, _, isPt_add p 𝒮 hℒ (isPt_liftTo p 𝒮 hℒ hπs hP₁ w k₁)
    (isPt_liftTo p 𝒮 hℒ hπs hP₂ w k₂), ?_, coords_liftTo p 𝒮 hℒ hC₁ w k₁, coords_liftTo p 𝒮 hℒ hC₂ w k₂⟩
  rw [raiseEt_mul]
  exact isEt_mul p 𝒮 hE₁' hE₂'

open Classical in

def μ (g : Type u) [CommRing g] [Algebra 𝓞 g] (x y : Fin 𝒮.d → g) : Fin 𝒮.d → g :=
  if h : ((p : g) ∈ nonZeroDivisors g ∧ IsAdicComplete (Ideal.span {(p : g)}) g) ∧ (IsRad p 𝒮 x ∧ IsRad p 𝒮 y) then
    Θinv p 𝒮 hREP g h.1.1 h.1.2
      (Θpt p 𝒮 hℒ hREP' g h.1.1 h.1.2 (unitEt p 𝒮 g 0) x h.2.1 + Θpt p 𝒮 hℒ hREP' g h.1.1 h.1.2 (unitEt p 𝒮 g 0) y h.2.2)
      (add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _))
      ((Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _))
  else x

section MuLaws

variable {g : Type u} [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
  (hcg : IsAdicComplete (Ideal.span {(p : g)}) g)

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
theorem μ_eq {x y : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hy : IsRad p 𝒮 y) :
    μ p 𝒮 hℒ hREP hREP' g x y = Θinv p 𝒮 hREP g hpg hcg
      (Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) x hx + Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) y hy)
      (add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _))
      ((Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _)) := by
  have h : ((p : g) ∈ nonZeroDivisors g ∧ IsAdicComplete (Ideal.span {(p : g)}) g) ∧ (IsRad p 𝒮 x ∧ IsRad p 𝒮 y) :=
    ⟨⟨hpg, hcg⟩, hx, hy⟩
  rw [μ, dif_pos h]

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hpg hcg in
theorem μ_rad {x y : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hy : IsRad p 𝒮 y) : IsRad p 𝒮 (μ p 𝒮 hℒ hREP hREP' g x y) := by
  rw [μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hx hy]
  exact Θinv_rad p 𝒮 hREP hpg hcg _ _ _

include hπs in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem Θpt_add_Θpt_eq {x y : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hy : IsRad p 𝒮 y) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) x hx + Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) y hy =
      Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) (μ p 𝒮 hℒ hREP hREP' g x y)
        (μ_rad p 𝒮 hℒ hREP hREP' hpg hcg hx hy) := by
  obtain ⟨w, hw, f₁, f₂, e, hP, hE, -, -⟩ := exists_descr_add p hπs 𝒮 hℒ hREP' hpg hcg (unitEt p 𝒮 g 0)
    (unitEt p 𝒮 g 0) hx hy
  rw [unitEt_convMul, WithConv.ofConv_toConv] at hE
  have key := eq_Θpt_Θinv p hπs 𝒮 hℒ hREP hREP' hpg hcg (add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _)
    (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _)) ((Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _))
    (unitEt p 𝒮 g 0) hw hP hE
  rw [key]
  congr 1
  exact (μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hx hy).symm

end MuLaws

end Push

section Laws

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
  (hπ : ∀ v, Surjective (π v))
  (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
  (𝒮 : SplitCoordinates p r H₁ G s π) (hℒ : 𝒮.Lawful) (hREP : HREP p 𝒮) (hREP' : HREP' p 𝒮)
  {g : Type u} [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
  (hcg : IsAdicComplete (Ideal.span {(p : g)}) g)

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hℒ hπs in

theorem Θpt_unitEt (v : ℕ) {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g v) x hx = Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) x hx := by
  rw [← raiseEt_unit p 𝒮 g 0 v (Nat.zero_le _), Θpt_raiseEt p hπs 𝒮 hℒ hREP' hpg hcg]

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hπs in
include hpg hcg in
theorem μ_zero_right {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) : μ p 𝒮 hℒ hREP hREP' g x 0 = x := by
  have h0 : IsRad p 𝒮 (0 : Fin 𝒮.d → g) := fun _ => Ideal.zero_mem _
  rw [μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hx h0,
    Θinv_congr p 𝒮 hREP hpg hcg _ _ _ (Θpt_mem p 𝒮 hℒ hREP' hpg hcg _ x hx) (Θpt_cont p 𝒮 hℒ hREP' hpg hcg _ x hx)
      (by rw [Θpt_unit_zero p hπs 𝒮 hℒ hREP' hpg hcg, add_zero]),
    Θinv_Θpt p 𝒮 hℒ hREP hREP' hpg hcg]

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hπs in
include hpg hcg in
theorem μ_zero_left {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) : μ p 𝒮 hℒ hREP hREP' g 0 x = x := by
  have h0 : IsRad p 𝒮 (0 : Fin 𝒮.d → g) := fun _ => Ideal.zero_mem _
  rw [μ_eq p 𝒮 hℒ hREP hREP' hpg hcg h0 hx,
    Θinv_congr p 𝒮 hREP hpg hcg _ _ _ (Θpt_mem p 𝒮 hℒ hREP' hpg hcg _ x hx) (Θpt_cont p 𝒮 hℒ hREP' hpg hcg _ x hx)
      (by rw [Θpt_unit_zero p hπs 𝒮 hℒ hREP' hpg hcg, zero_add]),
    Θinv_Θpt p 𝒮 hℒ hREP hREP' hpg hcg]

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hpg hcg in
theorem μ_comm {x y : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hy : IsRad p 𝒮 y) :
    μ p 𝒮 hℒ hREP hREP' g x y = μ p 𝒮 hℒ hREP hREP' g y x := by
  rw [μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hx hy, μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hy hx]
  exact Θinv_congr p 𝒮 hREP hpg hcg _ _ _ _ _ (add_comm _ _)

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hπs in
include hpg hcg in
theorem μ_assoc {x y z : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) (hy : IsRad p 𝒮 y) (hz : IsRad p 𝒮 z) :
    μ p 𝒮 hℒ hREP hREP' g (μ p 𝒮 hℒ hREP hREP' g x y) z = μ p 𝒮 hℒ hREP hREP' g x (μ p 𝒮 hℒ hREP hREP' g y z) := by
  have hxy := μ_rad p 𝒮 hℒ hREP hREP' hpg hcg hx hy
  have hyz := μ_rad p 𝒮 hℒ hREP hREP' hpg hcg hy hz
  rw [μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hxy hz, μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hx hyz]
  refine Θinv_congr p 𝒮 hREP hpg hcg _ _ _ _ _ ?_
  rw [← Θpt_add_Θpt_eq p hπs 𝒮 hℒ hREP hREP' hpg hcg hx hy, ← Θpt_add_Θpt_eq p hπs 𝒮 hℒ hREP hREP' hpg hcg hy hz,
    add_assoc]

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem comp_unitEt {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] (φ : g →ₐ[𝓞] g') (v : ℕ) :
    φ.comp (unitEt p 𝒮 g v) = unitEt p 𝒮 g' v :=
  AlgHom.ext fun t => φ.commutes _

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem comp_raiseEt {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] (φ : g →ₐ[𝓞] g') {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) :
    ∀ (w : ℕ) (hw : v ≤ w), φ.comp (raiseEt p 𝒮 y w hw) = raiseEt p 𝒮 (φ.comp y) w hw := by
  intro w
  induction w with
  | zero => intro h; obtain rfl := Nat.le_zero.mp h; simp only [raiseEt, liftToR_self]
  | succ w ih =>
    intro h
    by_cases hv : v = w + 1
    · subst hv; simp only [raiseEt, liftToR_self]
    · simp only [raiseEt, liftToR_succ _ (show v ≤ w by omega) h]
      rw [← AlgHom.comp_assoc]
      exact congrArg (fun ψ => AlgHom.comp ψ _) (ih (by omega))

include hker hℒ hπs in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem push_Θpt {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] (hpg' : (p : g') ∈ nonZeroDivisors g')
    (hcg' : IsAdicComplete (Ideal.span {(p : g')}) g') (φ : g →ₐ[𝓞] g') {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g)
    {x : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x) :
    push p φ (Θpt p 𝒮 hℒ hREP' g hpg hcg y x hx) =
      Θpt p 𝒮 hℒ hREP' g' hpg' hcg' (φ.comp y) (φ ∘ x) (fun j => map_mem_radical p φ (hx j)) := by
  haveI := hcg; haveI := hcg'
  obtain ⟨f, e, hP, hE, hC⟩ := Θpt_descr p 𝒮 hℒ hREP' hpg hcg y x hx
  have hL := (Θpt_clauses p 𝒮 hℒ hREP' hpg hcg y x hx _ f e _ hP hE).2
  obtain ⟨-, -, hPφ, hEφ, hCφ, hLφ⟩ :=
    push_descr p hker 𝒮 hℒ hpg' φ (Θpt_mem p 𝒮 hℒ hREP' hpg hcg y x hx) hx hP hE hC hL
  rw [comp_raiseEt] at hEφ hLφ
  exact eq_Θpt p hπs 𝒮 hℒ hREP' hpg' hcg' (φ.comp y) _ _ hPφ hEφ hCφ hLφ

include hker hunipG hπ hℒ hπs in

theorem Θinv_push_add {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] (hpg' : (p : g') ∈ nonZeroDivisors g')
    (hcg' : IsAdicComplete (Ideal.span {(p : g')}) g') (φ : g →ₐ[𝓞] g') {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g)
    {x₁ x₂ : Fin 𝒮.d → g} (hx₁ : IsRad p 𝒮 x₁) (hx₂ : IsRad p 𝒮 x₂)
    (hz' : push p φ (Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ x₁ hx₁ + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ x₂ hx₂) ∈ Fun p H₁ g')
    (hzc' : Cont p (push p φ (Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ x₁ hx₁ + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ x₂ hx₂))) :
    Θinv p 𝒮 hREP g' hpg' hcg' _ hz' hzc' =
      φ ∘ Θinv p 𝒮 hREP g hpg hcg (Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ x₁ hx₁ + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ x₂ hx₂)
        (add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _))
        ((Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _)) := by
  haveI := hcg; haveI := hcg'
  symm
  refine eq_Θinv p 𝒮 hREP hpg' hcg' _ hz' hzc' (fun j => map_mem_radical p φ (Θinv_rad p 𝒮 hREP hpg hcg _ _ _ j)) ?_
  obtain ⟨w, hw, f₁, f₂, e, hP, hE, -, -⟩ := exists_descr_add p hπs 𝒮 hℒ hREP' hpg hcg y₁ y₂ hx₁ hx₂
  exact clauses_push p hker hunipG hπ hπs 𝒮 hℒ hpg' φ (add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _)
    (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _)) (Θinv_rad p 𝒮 hREP hpg hcg _ _ _) hP hE (Θinv_clauses p 𝒮 hREP hpg hcg _ _ _)

include hker hunipG hπ hℒ hπs in
include hpg hcg in
theorem μ_nat {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] (hpg' : (p : g') ∈ nonZeroDivisors g')
    (hcg' : IsAdicComplete (Ideal.span {(p : g')}) g') (φ : g →ₐ[𝓞] g') {x y : Fin 𝒮.d → g} (hx : IsRad p 𝒮 x)
    (hy : IsRad p 𝒮 y) :
    μ p 𝒮 hℒ hREP hREP' g' (φ ∘ x) (φ ∘ y) = φ ∘ μ p 𝒮 hℒ hREP hREP' g x y := by
  have hx' : IsRad p 𝒮 (φ ∘ x) := fun j => map_mem_radical p φ (hx j)
  have hy' : IsRad p 𝒮 (φ ∘ y) := fun j => map_mem_radical p φ (hy j)
  rw [μ_eq p 𝒮 hℒ hREP hREP' hpg' hcg' hx' hy', μ_eq p 𝒮 hℒ hREP hREP' hpg hcg hx hy]
  have hsum : Θpt p 𝒮 hℒ hREP' g' hpg' hcg' (unitEt p 𝒮 g' 0) (φ ∘ x) hx' +
      Θpt p 𝒮 hℒ hREP' g' hpg' hcg' (unitEt p 𝒮 g' 0) (φ ∘ y) hy' =
      push p φ (Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) x hx + Θpt p 𝒮 hℒ hREP' g hpg hcg (unitEt p 𝒮 g 0) y hy) := by
    rw [push_add, push_Θpt p hker hπs 𝒮 hℒ hREP' hpg hcg hpg' hcg' φ, push_Θpt p hker hπs 𝒮 hℒ hREP' hpg hcg hpg' hcg' φ,
      comp_unitEt]
  rw [Θinv_congr p 𝒮 hREP hpg' hcg' _ _ _ ?_ ?_ hsum, Θinv_push_add p hker hunipG hπ hπs 𝒮 hℒ hREP hREP' hpg hcg hpg' hcg' φ]
  · rw [← hsum]; exact add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _)
  · rw [← hsum]; exact (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _)

def cEt {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) : Fin 𝒮.d → g :=
  Θinv p 𝒮 hREP g hpg hcg
    (Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ 0 (fun _ => Ideal.zero_mem _) + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ 0 (fun _ => Ideal.zero_mem _))
    (add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _))
    ((Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _))

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
theorem cEt_rad {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) : IsRad p 𝒮 (cEt p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂) :=
  Θinv_rad p 𝒮 hREP hpg hcg _ _ _

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
theorem cEt_comm {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) :
    cEt p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂ = cEt p 𝒮 hℒ hREP hREP' hpg hcg y₂ y₁ :=
  Θinv_congr p 𝒮 hREP hpg hcg _ _ _ _ _ (add_comm _ _)

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hπs in

theorem cEt_unit_right {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) : cEt p 𝒮 hℒ hREP hREP' hpg hcg y (unitEt p 𝒮 g v) = 0 := by
  rw [cEt, Θinv_congr p 𝒮 hREP hpg hcg _ _ _ (Θpt_mem p 𝒮 hℒ hREP' hpg hcg y 0 (fun _ => Ideal.zero_mem _))
      (Θpt_cont p 𝒮 hℒ hREP' hpg hcg y 0 (fun _ => Ideal.zero_mem _))
      (by rw [Θpt_unit_zero p hπs 𝒮 hℒ hREP' hpg hcg, add_zero]),
    Θinv_Θpt p 𝒮 hℒ hREP hREP' hpg hcg]

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in
include hπs in
theorem cEt_unit_left {v : ℕ} (y : 𝒮.Et v →ₐ[𝓞] g) : cEt p 𝒮 hℒ hREP hREP' hpg hcg (unitEt p 𝒮 g v) y = 0 := by
  rw [cEt_comm, cEt_unit_right p hπs]

include hker hunipG hπ hℒ hπs in

theorem comp_cEt {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] (hpg' : (p : g') ∈ nonZeroDivisors g')
    (hcg' : IsAdicComplete (Ideal.span {(p : g')}) g') (φ : g →ₐ[𝓞] g') {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) :
    φ ∘ cEt p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂ = cEt p 𝒮 hℒ hREP hREP' hpg' hcg' (φ.comp y₁) (φ.comp y₂) := by
  have hsum : Θpt p 𝒮 hℒ hREP' g' hpg' hcg' (φ.comp y₁) 0 (fun _ => Ideal.zero_mem _) +
      Θpt p 𝒮 hℒ hREP' g' hpg' hcg' (φ.comp y₂) 0 (fun _ => Ideal.zero_mem _) =
      push p φ (Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ 0 (fun _ => Ideal.zero_mem _) +
        Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ 0 (fun _ => Ideal.zero_mem _)) := by
    rw [push_add, push_Θpt p hker hπs 𝒮 hℒ hREP' hpg hcg hpg' hcg' φ, push_Θpt p hker hπs 𝒮 hℒ hREP' hpg hcg hpg' hcg' φ]
    congr 1 <;> congr 1 <;> funext j <;> exact (map_zero φ).symm
  rw [cEt, cEt, Θinv_congr p 𝒮 hREP hpg' hcg' _ _ _ ?_ ?_ hsum,
    Θinv_push_add p hker hunipG hπ hπs 𝒮 hℒ hREP hREP' hpg hcg hpg' hcg' φ]
  · rw [← hsum]; exact add_mem (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP' _ _ _ _ _)
  · rw [← hsum]; exact (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP' _ _ _ _ _)

include hπs in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem Θpt_zero_add_Θpt_zero {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ 0 (fun _ => Ideal.zero_mem _) + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ 0 (fun _ => Ideal.zero_mem _) =
      Θpt p 𝒮 hℒ hREP' g hpg hcg (WithConv.toConv y₁ * WithConv.toConv y₂).ofConv
        (cEt p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂) (cEt_rad p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂) := by
  obtain ⟨w, hw, f₁, f₂, e, hP, hE, -, -⟩ := exists_descr_add p hπs 𝒮 hℒ hREP' hpg hcg y₁ y₂
    (x₁ := 0) (x₂ := 0) (fun _ => Ideal.zero_mem _) (fun _ => Ideal.zero_mem _)
  exact eq_Θpt_Θinv p hπs 𝒮 hℒ hREP hREP' hpg hcg _ _ _ hw hP hE

include hπs in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)] in

theorem Θpt_add_Θpt {v : ℕ} (y₁ y₂ : 𝒮.Et v →ₐ[𝓞] g) {x₁ x₂ : Fin 𝒮.d → g} (hx₁ : IsRad p 𝒮 x₁)
    (hx₂ : IsRad p 𝒮 x₂) :
    Θpt p 𝒮 hℒ hREP' g hpg hcg y₁ x₁ hx₁ + Θpt p 𝒮 hℒ hREP' g hpg hcg y₂ x₂ hx₂ =
      Θpt p 𝒮 hℒ hREP' g hpg hcg (WithConv.toConv y₁ * WithConv.toConv y₂).ofConv
        (μ p 𝒮 hℒ hREP hREP' g (cEt p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂) (μ p 𝒮 hℒ hREP hREP' g x₁ x₂))
        (μ_rad p 𝒮 hℒ hREP hREP' hpg hcg (cEt_rad p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂)
          (μ_rad p 𝒮 hℒ hREP hREP' hpg hcg hx₁ hx₂)) := by
  have hm := μ_rad p 𝒮 hℒ hREP hREP' hpg hcg hx₁ hx₂
  have hc := cEt_rad p 𝒮 hℒ hREP hREP' hpg hcg y₁ y₂
  rw [Θpt_eq_add p hπs 𝒮 hℒ hREP' hpg hcg y₁ hx₁, Θpt_eq_add p hπs 𝒮 hℒ hREP' hpg hcg y₂ hx₂, add_add_add_comm,
    Θpt_unitEt p hπs 𝒮 hℒ hREP' hpg hcg v hx₁, Θpt_unitEt p hπs 𝒮 hℒ hREP' hpg hcg v hx₂,
    Θpt_add_Θpt_eq p hπs 𝒮 hℒ hREP hREP' hpg hcg hx₁ hx₂, Θpt_zero_add_Θpt_zero p hπs 𝒮 hℒ hREP hREP' hpg hcg,
    Θpt_eq_add p hπs 𝒮 hℒ hREP' hpg hcg _ hc, add_assoc, Θpt_unitEt p hπs 𝒮 hℒ hREP' hpg hcg v hc,
    Θpt_add_Θpt_eq p hπs 𝒮 hℒ hREP hREP' hpg hcg hc hm, ← Θpt_unitEt p hπs 𝒮 hℒ hREP' hpg hcg v,
    ← Θpt_eq_add p hπs 𝒮 hℒ hREP' hpg hcg]

end Laws

end Deformation.HondaSystem.MixedLaw

end

namespace Deformation
p2m_export "Deformation" "HondaSystem DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map SpecialFibre.reduction_apply SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.map DieudonneModule.eval DieudonneModule.eval_convMul DieudonneModule.eval_convOne DieudonneModule.eval_comp_bialgHom PLoc.mapLinear PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero HondaSystem.fontaineFunctor HondaSystem.SplitCoordinates DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual HondaSystem.SplitCoordinates.map_mem_fontaineFunctor_and_described HondaSystem.SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor SplitCoordinates SplitCoordinates.map_mem_fontaineFunctor_and_described SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X"
namespace MixedLaw
p2m_open "Deformation.HondaSystem Deformation"

section Final

open Function

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
  [Algebra 𝓞 (ZMod p)]
  {r : ℕ} {H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)}
  {G : ℕ → Type v} [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  {s : ∀ v, G (v + 1) →ₐc[ZMod p] G v}
  {π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v)}
  (𝒮 : SplitCoordinates p r H₁ G s π)

theorem isRad_of_isNilpotent {g : Type u} [CommRing g] {x : Fin 𝒮.d → g} (hx : ∀ j, IsNilpotent (x j)) : IsRad p 𝒮 x :=
  fun j => by obtain ⟨n, hn⟩ := hx j; exact ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩

theorem convMul_eq_lift_comp_comul {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ} (f f' : 𝒮.Et v →ₐ[𝓞] g) :
    (WithConv.toConv f * WithConv.toConv f').ofConv =
      (Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v)) :=
  AlgHom.ext fun t => by rw [AlgHom.convMul_apply]; rfl

theorem lift_comp_includeLeft' {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ} (f f' : 𝒮.Et v →ₐ[𝓞] g) :
    (Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.includeLeft : 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v) = f :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

theorem lift_comp_includeRight' {g : Type u} [CommRing g] [Algebra 𝓞 g] {v : ℕ} (f f' : 𝒮.Et v →ₐ[𝓞] g) :
    (Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.includeRight : 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v) = f' :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

theorem map_comp_includeLeft' {v : ℕ} :
    (Algebra.TensorProduct.map (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v) (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v)).comp
      (Algebra.TensorProduct.includeLeft : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1)) =
      raiseEt p 𝒮 (Algebra.TensorProduct.includeLeft : 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v) (v + 1) (Nat.le_succ v) := by
  rw [raiseEt, liftToR_succ _ le_rfl, liftToR_self]
  exact AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul, map_one]

theorem map_comp_includeRight' {v : ℕ} :
    (Algebra.TensorProduct.map (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v) (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v)).comp
      (Algebra.TensorProduct.includeRight : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1)) =
      raiseEt p 𝒮 (Algebra.TensorProduct.includeRight : 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v) (v + 1) (Nat.le_succ v) := by
  rw [raiseEt, liftToR_succ _ le_rfl, liftToR_self]
  exact AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]

theorem map_st_cEt_includes (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v))) (hπ : ∀ v, Surjective (π v))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (hℒ : 𝒮.Lawful) (hREP : HREP p 𝒮) (hREP' : HREP' p 𝒮) (v : ℕ)
    (hpg₁ : (p : 𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1)) ∈ nonZeroDivisors (𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1)))
    (hcg₁ : IsAdicComplete (Ideal.span {(p : 𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1))}) (𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1)))
    (hpg₀ : (p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v) ∈ nonZeroDivisors (𝒮.Et v ⊗[𝓞] 𝒮.Et v))
    (hcg₀ : IsAdicComplete (Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)}) (𝒮.Et v ⊗[𝓞] 𝒮.Et v)) :
    (Algebra.TensorProduct.map (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v) (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v)) ∘
        cEt p 𝒮 hℒ hREP hREP' hpg₁ hcg₁
          (Algebra.TensorProduct.includeLeft : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1))
          (Algebra.TensorProduct.includeRight : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et (v + 1) ⊗[𝓞] 𝒮.Et (v + 1)) =
      cEt p 𝒮 hℒ hREP hREP' hpg₀ hcg₀
        (Algebra.TensorProduct.includeLeft : 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
        (Algebra.TensorProduct.includeRight : 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v) := by
  rw [comp_cEt p hker hunipG hπ hπs 𝒮 hℒ hREP hREP' hpg₁ hcg₁ hpg₀ hcg₀, map_comp_includeLeft', map_comp_includeRight']
  exact Θinv_congr p 𝒮 hREP hpg₀ hcg₀ _ _ _ _ _ (by rw [Θpt_raiseEt p hπs 𝒮 hℒ hREP', Θpt_raiseEt p hπs 𝒮 hℒ hREP'])

end Final

end Deformation.HondaSystem.MixedLaw

open Deformation.HondaSystem.MixedLaw in

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

    (hREP : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g →
      ∀ z : (H₁.L →ₗ[𝓞] Localization.Away (p : g)) ×
      ((Fin r → 𝓞) →+ Deformation.UnipotentWittCovector p (TensorProduct 𝓞 (ZMod p) g)),
      z ∈ Deformation.HondaSystem.fontaineFunctor p H₁ (ZMod p)
      (Algebra.TensorProduct.includeRight : g →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) g).toRingHom →
      (∃ v₀ : ℕ, ∀ m : Fin r → 𝓞, z.2 ((p : 𝓞) ^ v₀ • m) = 0) →
      ∃! x : Fin 𝒮.d → g, (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) ∧
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
              Deformation.PLoc.wSeries p (fun k => y (𝒮.ĉ i k v)))))
    (hREP' : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g →
      ∀ (v₁ : ℕ) (y₁ : 𝒮.Et v₁ →ₐ[𝓞] g) (x : Fin 𝒮.d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) →
      (∃ f : 𝒮.Gc v₁ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) g, ∀ i, f (𝒮.κ v₁ (X i)) = (1 : ZMod p) ⊗ₜ[𝓞] x i) →
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
              Deformation.PLoc.wSeries p (fun k => y (𝒮.ĉ i k v))))) :
    ∃ (Φ : MvFormalGroup 𝒮.d 𝓞) (_ : Φ.IsComm) (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v),

      Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀ ∧

      (∀ v i, Algebra.TensorProduct.map (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v)
          (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v) (c₂ (v + 1) i) = c₂ v i) ∧
      (∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)}) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f : 𝒮.Et v →ₐ[𝓞] g) (j : Fin 𝒮.d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))) (fun _ _ => Commute.all _ _) (c₂ v j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))) f (fun _ _ => Commute.all _ _) (c₂ v j) = 0) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (j : Fin 𝒮.d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ v j)) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' f'' : 𝒮.Et v →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) f'' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i))) ∧

      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (x x' : Fin 𝒮.d → g),
          (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, x' j ∈ (Ideal.span {(p : g)}).radical) → ∀ i : Fin 𝒮.d,
          Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)})
              (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x) ((fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x') ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) (Φ.toPowerSeries i)) (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (𝒮.ĉ i k v)) =
          (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f (𝒮.ĉ i k v))) +
            (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x' (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f' (𝒮.ĉ i k v)))) := by
  classical
  have hREP₀ : HREP p 𝒮 := fun g _ _ hpg hcg z hz hzc => hREP g hpg hcg z hz hzc
  have hREP₀' : HREP' p 𝒮 := fun g _ _ hpg hcg v₁ y₁ x hx hf => hREP' g hpg hcg v₁ y₁ x hx hf
  have hfree_nzd : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g],
      (p : g) ∈ nonZeroDivisors g := fun g _ _ _ _ => nzd_of_free p hp g
  have hfree_cpl : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g],
      IsAdicComplete (Ideal.span {(p : g)}) g := fun g _ _ _ _ => isAdicComplete_of_free 𝓞 p g

  obtain ⟨Φ, ⟨hΦc, hΦμ⟩, -⟩ :=
    MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical p hp 𝒮.d
      (μ p 𝒮 hℒ hREP₀ hREP₀')
      (fun g _ _ hpg hcg x y hx hy => μ_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hx hy)
      (fun g _ _ hpg hcg x hx =>
        ⟨μ_zero_right p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg hx, μ_zero_left p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg hx⟩)
      (fun g _ _ hpg hcg x y z hx hy hz => μ_assoc p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg hx hy hz)
      (fun g _ _ hpg hcg x y hx hy => μ_comm p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hx hy)
      (fun g g' _ _ _ _ hpg hcg hpg' hcg' φ x y hx hy =>
        μ_nat p hker hunipG hπ hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg hpg' hcg' φ hx hy)
  have hμΦ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
      (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) (x y : Fin 𝒮.d → g), IsRad p 𝒮 x → IsRad p 𝒮 y →
      μ p 𝒮 hℒ hREP₀ hREP₀' g x y = fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) :=
    fun g _ _ hpg hcg x y hx hy => funext (hΦμ g hpg hcg x y hx hy)

  have hlift : Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀ := by
    refine Deformation.HondaSystem.SplitCoordinates.map_eq_phi0_of_forall_exists_convMul_apply_kappa_X p r H₁ G s π 𝒮
      hℒ Φ fun g _ _ _ _ x y hxn hyn => ?_
    have hpg := hfree_nzd g
    have hcg := hfree_cpl g
    have hx : IsRad p 𝒮 x := isRad_of_isNilpotent p 𝒮 hxn
    have hy : IsRad p 𝒮 y := isRad_of_isNilpotent p 𝒮 hyn
    obtain ⟨w, hw, f₁, f₂, e, hP, hE, hC₁, hC₂⟩ :=
      exists_descr_add p hπs 𝒮 hℒ hREP₀' hpg hcg (unitEt p 𝒮 g 0) (unitEt p 𝒮 g 0) hx hy
    rw [unitEt_convMul, WithConv.ofConv_toConv] at hE
    have hcl := (Θinv_clauses p 𝒮 hREP₀ hpg hcg _
      (add_mem (Θpt_mem p 𝒮 hℒ hREP₀' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP₀' _ _ _ _ _))
      ((Θpt_cont p 𝒮 hℒ hREP₀' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP₀' _ _ _ _ _)) _ _ e _ hP hE).1
    refine ⟨w, f₁, f₂, hC₁, hC₂, fun i => ?_⟩
    rw [hcl i, ← μ_eq p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hx hy, hΦμ g hpg hcg x y hx hy i]

  haveI hfEt : ∀ v, Module.Free 𝓞 (𝒮.Et v) := hℒ.free_Et
  haveI hfiEt : ∀ v, Module.Finite 𝓞 (𝒮.Et v) := hℒ.finite_Et
  have hpgv : ∀ v, (p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v) ∈ nonZeroDivisors (𝒮.Et v ⊗[𝓞] 𝒮.Et v) := fun v => hfree_nzd _
  have hcgv : ∀ v, IsAdicComplete (Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)}) (𝒮.Et v ⊗[𝓞] 𝒮.Et v) :=
    fun v => hfree_cpl _
  let ι₁ : ∀ v, 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v := fun v => Algebra.TensorProduct.includeLeft
  let ι₂ : ∀ v, 𝒮.Et v →ₐ[𝓞] 𝒮.Et v ⊗[𝓞] 𝒮.Et v := fun v => Algebra.TensorProduct.includeRight
  let c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v := fun v => cEt p 𝒮 hℒ hREP₀ hREP₀' (hpgv v) (hcgv v) (ι₁ v) (ι₂ v)

  have hc₂ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] (hpg : (p : g) ∈ nonZeroDivisors g)
      (hcg : IsAdicComplete (Ideal.span {(p : g)}) g) (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g),
      (fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j)) =
        cEt p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f' := by
    intro g _ _ hpg hcg v f f'
    have h := comp_cEt p hker hunipG hπ hπs 𝒮 hℒ hREP₀ hREP₀' (hpgv v) (hcgv v) hpg hcg
      (Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)) (ι₁ v) (ι₂ v)
    rw [lift_comp_includeLeft', lift_comp_includeRight'] at h
    exact h
  refine ⟨Φ, hΦc, c₂, hlift, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro v i
    exact congrFun (map_st_cEt_includes p 𝒮 hker hunipG hπ hπs hℒ hREP₀ hREP₀' v (hpgv (v + 1)) (hcgv (v + 1))
      (hpgv v) (hcgv v)) i

  · intro v i
    obtain ⟨w, hw, f₁, f₂, e, hP, hE, hC₁, hC₂⟩ := exists_descr_add p hπs 𝒮 hℒ hREP₀' (hpgv v) (hcgv v) (ι₁ v) (ι₂ v)
      (x₁ := 0) (x₂ := 0) (fun _ => Ideal.zero_mem _) (fun _ => Ideal.zero_mem _)
    rw [eq_of_coords_eq p 𝒮 hℒ hC₁ (coords_unitGc_zero p 𝒮 hℒ _ w),
      eq_of_coords_eq p 𝒮 hℒ hC₂ (coords_unitGc_zero p 𝒮 hℒ _ w), unitGc_convMul, WithConv.ofConv_toConv] at hP
    have hcl := (Θinv_clauses p 𝒮 hREP₀ (hpgv v) (hcgv v) _
      (add_mem (Θpt_mem p 𝒮 hℒ hREP₀' _ _ _ _ _) (Θpt_mem p 𝒮 hℒ hREP₀' _ _ _ _ _))
      ((Θpt_cont p 𝒮 hℒ hREP₀' _ _ _ _ _).add (Θpt_cont p 𝒮 hℒ hREP₀' _ _ _ _ _)) _ _ e _ hP hE).1 i
    have h0 : (1 : ZMod p) ⊗ₜ[𝓞] c₂ v i = 0 := hcl.symm.trans (by
      show algebraMap (ZMod p) (TensorProduct 𝓞 (ZMod p) (𝒮.Et v ⊗[𝓞] 𝒮.Et v))
        (Coalgebra.counit (R := ZMod p) (𝒮.κ w (X i))) = 0
      rw [hℒ.counit_κ_X, map_zero])
    rw [← Deformation.SpecialFibre.ker_reduction_eq_span (𝓞 := 𝓞) (k := ZMod p) (ℛ := 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
      (ZMod.ringHom_surjective _) hker, RingHom.mem_ker, Deformation.SpecialFibre.reduction_apply]
    exact h0

  · intro g _ _ hpg hcg v f j
    haveI := hcg
    constructor
    · have h := congrFun (hc₂ g hpg hcg v f (unitEt p 𝒮 g v)) j
      rw [cEt_unit_right p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg] at h
      exact h
    · have h := congrFun (hc₂ g hpg hcg v (unitEt p 𝒮 g v) f) j
      rw [cEt_unit_left p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg] at h
      exact h

  · intro g _ _ hpg hcg v f f' j
    haveI := hcg
    have h := (hc₂ g hpg hcg v f f').trans ((cEt_comm p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f').trans (hc₂ g hpg hcg v f' f).symm)
    exact congrFun h j

  · intro g _ _ hpg hcg v f f' f''
    haveI := hcg
    have h0 : IsRad p 𝒮 (0 : Fin 𝒮.d → g) := fun _ => Ideal.zero_mem _

    have key := add_assoc (Θpt p 𝒮 hℒ hREP₀' g hpg hcg f 0 h0) (Θpt p 𝒮 hℒ hREP₀' g hpg hcg f' 0 h0)
      (Θpt p 𝒮 hℒ hREP₀' g hpg hcg f'' 0 h0)
    rw [Θpt_zero_add_Θpt_zero p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f',
      Θpt_zero_add_Θpt_zero p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg f' f'',
      Θpt_add_Θpt p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg, Θpt_add_Θpt p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg] at key
    have key2 := Θinv_congr p 𝒮 hREP₀ hpg hcg _ (Θpt_mem p 𝒮 hℒ hREP₀' _ _ _ _ _) (Θpt_cont p 𝒮 hℒ hREP₀' _ _ _ _ _)
      (Θpt_mem p 𝒮 hℒ hREP₀' _ _ _ _ _) (Θpt_cont p 𝒮 hℒ hREP₀' _ _ _ _ _) key
    rw [Θinv_Θpt p 𝒮 hℒ hREP₀ hREP₀' hpg hcg, Θinv_Θpt p 𝒮 hℒ hREP₀ hREP₀' hpg hcg,
      μ_zero_right p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f'),
      μ_zero_left p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f' f''),
      μ_comm p 𝒮 hℒ hREP₀ hREP₀' hpg hcg (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _) (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _)]
      at key2

    rw [← convMul_eq_lift_comp_comul p 𝒮 f f', ← convMul_eq_lift_comp_comul p 𝒮 f' f'', hc₂ g hpg hcg v, hc₂ g hpg hcg v,
      hc₂ g hpg hcg v, hc₂ g hpg hcg v,
      ← hμΦ g hpg hcg _ _ (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _) (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _),
      ← hμΦ g hpg hcg _ _ (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _) (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _), key2,
      μ_comm p 𝒮 hℒ hREP₀ hREP₀' hpg hcg (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _) (cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg _ _)]

  · intro g _ _ hpg hcg v f f' x x' hx hx' i
    haveI := hcg
    have hxr : IsRad p 𝒮 x := hx
    have hxr' : IsRad p 𝒮 x' := hx'
    have hc := cEt_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f'
    have hm := μ_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hxr hxr'
    have hm' := μ_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hxr' hc

    have eqR := Θpt_add_Θpt p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f' hxr hxr'
    obtain ⟨fr, er, hPr, hEr, hCr⟩ := Θpt_descr p 𝒮 hℒ hREP₀' hpg hcg (WithConv.toConv f * WithConv.toConv f').ofConv
      (μ p 𝒮 hℒ hREP₀ hREP₀' g (cEt p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f') (μ p 𝒮 hℒ hREP₀ hREP₀' g x x'))
      (μ_rad p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hc hm)
    have hLr := (logCl_raiseEt_iff p 𝒮 hℒ _ (le_max_left _ _)).1
      (Θpt_clauses p 𝒮 hℒ hREP₀' hpg hcg _ _ _ _ fr er _ hPr hEr).2 i

    obtain ⟨f₁, e₁, hP₁, hE₁, -⟩ := Θpt_descr p 𝒮 hℒ hREP₀' hpg hcg f x hxr
    have hL₁ := (logCl_raiseEt_iff p 𝒮 hℒ _ (le_max_left _ _)).1 (Θpt_clauses p 𝒮 hℒ hREP₀' hpg hcg _ _ _ _ f₁ e₁ _ hP₁ hE₁).2 i
    obtain ⟨f₂, e₂, hP₂, hE₂, -⟩ := Θpt_descr p 𝒮 hℒ hREP₀' hpg hcg f' x' hxr'
    have hL₂ := (logCl_raiseEt_iff p 𝒮 hℒ _ (le_max_left _ _)).1 (Θpt_clauses p 𝒮 hℒ hREP₀' hpg hcg _ _ _ _ f₂ e₂ _ hP₂ hE₂).2 i

    have hperm : μ p 𝒮 hℒ hREP₀ hREP₀' g (cEt p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f') (μ p 𝒮 hℒ hREP₀ hREP₀' g x x') =
        μ p 𝒮 hℒ hREP₀ hREP₀' g x (μ p 𝒮 hℒ hREP₀ hREP₀' g x' (cEt p 𝒮 hℒ hREP₀ hREP₀' hpg hcg f f')) := by
      rw [μ_comm p 𝒮 hℒ hREP₀ hREP₀' hpg hcg hc hm, μ_assoc p hπs 𝒮 hℒ hREP₀ hREP₀' hpg hcg hxr hxr' hc]
    rw [← convMul_eq_lift_comp_comul p 𝒮 f f', hc₂ g hpg hcg v f f', ← hμΦ g hpg hcg _ _ hxr' hc,
      ← hμΦ g hpg hcg _ _ hxr hm', ← hperm, ← hLr, ← eqR, Prod.fst_add, LinearMap.add_apply, hL₁, hL₂]

end S_Deformation_HondaSystem_exists_mvFormalGroup_cocycle_of_splitCoordinates
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_mvFormalGroup_cocycle_of_splitCoordinates (solution)
