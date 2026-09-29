-- Prove2me | solution 1 for Deformation.HondaSystem.map_apply_basis_mem_fontaineHodge_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/db7e8eb8-2c3c-5724-98db-259436b6a7ae

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
import Theorems.Thm_Deformation_FontaineLift_isPadicLimit_wPartialSum_adicEval
import Theorems.Thm_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.map fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.toCovector_map DieudonneModule.toCovector_mem_wKer_iff DieudonneModule.eval DieudonneModule.eval_apply DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero UnipotentWittCovector.w_map UnipotentWittCovector.w_eq_zero_iff_mem_wKer HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace LVe
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

end Deformation.HondaSystem.LVe

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.map fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.toCovector_map DieudonneModule.toCovector_mem_wKer_iff DieudonneModule.eval DieudonneModule.eval_apply DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero UnipotentWittCovector.w_map UnipotentWittCovector.w_eq_zero_iff_mem_wKer HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace LVe
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

end Deformation.HondaSystem.LVe

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.map fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.toCovector_map DieudonneModule.toCovector_mem_wKer_iff DieudonneModule.eval DieudonneModule.eval_apply DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero UnipotentWittCovector.w_map UnipotentWittCovector.w_eq_zero_iff_mem_wKer HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace LVe
p2m_open "Deformation.HondaSystem Deformation"

open MvPowerSeries

theorem natCast_mem_nonZeroDivisors {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (R : Type*) [CommRing R] [Algebra 𝓞 R] [Module.Free 𝓞 R] : (p : R) ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  set b := Module.Free.chooseBasis 𝓞 R
  have hpx : (p : 𝓞) • x = 0 := by
    rw [Algebra.smul_def, map_natCast, mul_comm]
    exact hx
  have hrepr : b.repr x = 0 := by
    ext i
    have hi := congrArg (fun y => b.repr y i) hpx
    simp only [map_smul, map_zero, Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] at hi
    exact (mem_nonZeroDivisors_iff_right.1 hp) _ (by rw [mul_comm]; exact hi)
  exact b.repr.map_eq_zero_iff.1 hrepr

theorem map_mem_span_natCast' {B C : Type*} [CommRing B] [CommRing C] {Φ : Type*} [FunLike Φ B C]
    [RingHomClass Φ B C] (φ : Φ) (p : ℕ) {t : B} (ht : t ∈ Ideal.span {(p : B)}) :
    φ t ∈ Ideal.span {(p : C)} := by
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem map_mem_radical_of_mem_radical {B C : Type*} [CommRing B] [CommRing C] {Φ : Type*} [FunLike Φ B C]
    [RingHomClass Φ B C] (φ : Φ) (p : ℕ) {t : B} (ht : t ∈ (Ideal.span {(p : B)}).radical) :
    φ t ∈ (Ideal.span {(p : C)}).radical := by
  obtain ⟨n, hn⟩ := ht
  exact ⟨n, by rw [← map_pow]; exact map_mem_span_natCast' φ p hn⟩

section AdicEvalZero

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem adicEval_zero_eq_zero [Fintype σ] (J : Ideal S) [IsAdicComplete J S] {f : MvPowerSeries σ R}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvFormalGroup.adicEval J (fun _ : σ => (0 : S)) f = 0 := by
  letI : TopologicalSpace S := J.adicTopology
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  have h := hasSum_adicEval (R := R) J (x := fun _ : σ => (0 : S)) (fun _ => Ideal.zero_mem _) f
  have hzero : (fun e : σ →₀ ℕ => algebraMap R S (coeff e f) * e.prod fun s n => (0 : S) ^ n) = 0 := by
    funext e
    by_cases he : e = 0
    · subst he
      rw [Pi.zero_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero, zero_mul]
    · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact he (Finsupp.ext hcon)
      rw [Pi.zero_apply, Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs),
        mul_zero]
  rw [hzero] at h
  exact h.unique hasSum_zero

end AdicEvalZero

end Deformation.HondaSystem.LVe

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.map fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.toCovector_map DieudonneModule.toCovector_mem_wKer_iff DieudonneModule.eval DieudonneModule.eval_apply DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero UnipotentWittCovector.w_map UnipotentWittCovector.w_eq_zero_iff_mem_wKer HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace LVe
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

end Deformation.HondaSystem.LVe

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.map fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.toCovector_map DieudonneModule.toCovector_mem_wKer_iff DieudonneModule.eval DieudonneModule.eval_apply DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero UnipotentWittCovector.w_map UnipotentWittCovector.w_eq_zero_iff_mem_wKer HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace LVe
p2m_open "Deformation.HondaSystem Deformation"

p2m_open "Deformation P2MW.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle.Deformation Deformation.PLoc"

theorem exists_forall_wSeries_sub_wPartialSum_mem_pSub_of_forall_mem (p : ℕ) [Fact p.Prime]
    {g : Type u} [CommRing g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (c : ℕ → g) (n : ℕ) (hc : ∀ k, n ≤ k → c k ∈ Ideal.span {(p : g)}) :
    ∃ N : ℕ, ∀ n', N ≤ n' → wSeries p c - wPartialSum p c n' ∈ pSub p g := by
  obtain ⟨N, hN⟩ := Deformation.PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span p g c ⟨n, hc⟩ 1
  refine ⟨N, fun n' hn' => ?_⟩
  rw [← neg_sub]
  exact neg_mem (hN n' hn')

end Deformation.HondaSystem.LVe

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.coeff_map TruncWitt.coeff_shiftLE DieudonneModule DieudonneModule.map fontaineHodge SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shiftLE UnipotentWittCovector.map UnipotentWittCovector.map_of DieudonneModule.toCovector_map DieudonneModule.toCovector_mem_wKer_iff DieudonneModule.eval DieudonneModule.eval_apply DieudonneModule.eval_of DieudonneModule.eval_convMul DieudonneModule.eval_comp_bialgHom PLoc.invPow PLoc.invPow_mul_algebraMap_pow PLoc.invPow_add PLoc.pSub PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wPartialSum_zero PLoc.wSeries PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero WittGhost.divGhost WittGhost.divGhost_apply UnipotentWittCovector.wUp UnipotentWittCovector.wUp_of_truncate UnipotentWittCovector.wUp_of_zero UnipotentWittCovector.w_map UnipotentWittCovector.w_eq_zero_iff_mem_wKer HondaSystem.fontaineFunctor HondaSystem.fst_sub_wUp_mem_pSub HondaSystem.SplitCoordinates FontaineLift.isPadicLimit_wPartialSum_adicEval PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L fontaineFunctor fst_sub_wUp_mem_pSub SplitCoordinates"
namespace LVe
p2m_open "Deformation.HondaSystem Deformation"

p2m_open "Deformation P2MW.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle.Deformation"

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

end Deformation.HondaSystem.LVe

open scoped TensorProduct
open MvPowerSeries _root_.Deformation _root_.P2MW.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle.Deformation Deformation.HondaSystem.LVe in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (h𝒮 : 𝒮.Lawful)
    (Φ : MvFormalGroup 𝒮.d 𝓞) [Φ.IsComm]
    (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
    (hc₂p : ∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)})
    (hLOGA :
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (x x' : Fin 𝒮.d → g),
          (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, x' j ∈ (Ideal.span {(p : g)}).radical) → ∀ i : Fin 𝒮.d,
          Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)})
              (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x) ((fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x') ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) (Φ.toPowerSeries i)) (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (𝒮.ĉ i k v)) =
          (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f (𝒮.ĉ i k v))) +
            (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x' (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f' (𝒮.ĉ i k v)))))

    (v : ℕ) (Lv : Type u) [CommRing Lv] [HopfAlgebra 𝓞 Lv] [Module.Free 𝓞 Lv] [Module.Finite 𝓞 Lv]
    (ιv : 𝒮.Et v →ₐc[𝓞] Lv) (Ψv : MvPowerSeries (Fin 𝒮.d) 𝓞 →ₐ[𝓞] Lv)
    (hΨrad : ∀ i, Ψv (X i) ∈ (Ideal.span {(p : Lv)}).radical)
    (hΨeval : ∀ F, Ψv F = MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun i => Ψv (X i)) F)
    (hΨε : ∀ i, Coalgebra.counit (R := 𝓞) (Ψv (X i)) = 0)
    (hcomul : ∀ i, Coalgebra.comul (R := 𝓞) (Ψv (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
          (Sum.elim (fun j => Ψv (X j) ⊗ₜ[𝓞] (1 : Lv))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
              (Sum.elim (fun j => (1 : Lv) ⊗ₜ[𝓞] Ψv (X j))
                (fun j => Algebra.TensorProduct.map (ιv : 𝒮.Et v →ₐ[𝓞] Lv) (ιv : 𝒮.Et v →ₐ[𝓞] Lv)
                  (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i))
    (hkill : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 Lv (p ^ v) =
        (Algebra.ofId 𝓞 Lv).comp (Bialgebra.counitAlgHom 𝓞 Lv))

    (ee : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐc[ZMod p] ZMod p ⊗[𝓞] Lv)
    (heeκ : ∀ F : MvPowerSeries (Fin 𝒮.d) 𝓞,
        ee (𝒮.κ v (F.map (algebraMap 𝓞 (ZMod p))) ⊗ₜ[ZMod p] (1 : 𝒮.Ge v)) = (1 : ZMod p) ⊗ₜ[𝓞] Ψv F)
    (heeθ : ∀ y : 𝒮.Et v,
        ee ((1 : 𝒮.Gc v) ⊗ₜ[ZMod p] 𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] y)) = (1 : ZMod p) ⊗ₜ[𝓞] ιv y)
    (i : Fin 𝒮.d) :
    Deformation.DieudonneModule.map (ZMod p) p
        ((ee.comp (𝒮.Θ v)) : G v →ₐc[ZMod p] ZMod p ⊗[𝓞] Lv)
        (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) ∈
      Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : Lv →ₐ[𝓞] ZMod p ⊗[𝓞] Lv).toRingHom := by
  classical

  haveI hLc : IsAdicComplete (Ideal.span {(p : Lv)}) Lv :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p Lv
  haveI hLLc : IsAdicComplete (Ideal.span {(p : Lv ⊗[𝓞] Lv)}) (Lv ⊗[𝓞] Lv) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (Lv ⊗[𝓞] Lv)
  have hpL : (p : Lv) ∈ nonZeroDivisors Lv := natCast_mem_nonZeroDivisors p hp Lv
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  set redL : Lv →+* ZMod p ⊗[𝓞] Lv :=
    (Algebra.TensorProduct.includeRight : Lv →ₐ[𝓞] ZMod p ⊗[𝓞] Lv).toRingHom with hredL
  have hred_surj : Function.Surjective redL := SpecialFibre.reduction_surjective hk
  have hred_ker : RingHom.ker redL = Ideal.span {(p : Lv)} := SpecialFibre.ker_reduction_eq_span hk hker

  have hQrad : ∀ (Q : Lv →ₐ[𝓞] Lv) (j : Fin 𝒮.d), Q (Ψv (X j)) ∈ (Ideal.span {(p : Lv)}).radical :=
    fun Q j => map_mem_radical_of_mem_radical Q p (hΨrad j)

  have hconv_x : ∀ (Q Q' : Lv →ₐ[𝓞] Lv) (j : Fin 𝒮.d),
      (WithConv.toConv Q * WithConv.toConv Q').ofConv (Ψv (X j)) =
        MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
          (Sum.elim (fun j => Q (Ψv (X j)))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
              (Sum.elim (fun j => Q' (Ψv (X j)))
                (fun j => Algebra.TensorProduct.lift (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
                  (Q'.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (fun _ _ => Commute.all _ _) (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries j) := by
    intro Q Q' j
    have hin : ∀ t, Sum.elim (fun j => (1 : Lv) ⊗ₜ[𝓞] Ψv (X j))
        (fun j => Algebra.TensorProduct.map (ιv : 𝒮.Et v →ₐ[𝓞] Lv) (ιv : 𝒮.Et v →ₐ[𝓞] Lv) (c₂ v j)) t ∈
          (Ideal.span {(p : Lv ⊗[𝓞] Lv)}).radical := by
      rintro (j | j)
      · exact map_mem_radical_of_mem_radical
          (Algebra.TensorProduct.includeRight : Lv →ₐ[𝓞] Lv ⊗[𝓞] Lv) p (hΨrad j)
      · exact Ideal.le_radical (map_mem_span_natCast' _ p (hc₂p v j))
    have hout : ∀ t, Sum.elim (fun j => Ψv (X j) ⊗ₜ[𝓞] (1 : Lv))
        (fun j => MvFormalGroup.adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)})
          (Sum.elim (fun j => (1 : Lv) ⊗ₜ[𝓞] Ψv (X j))
            (fun j => Algebra.TensorProduct.map (ιv : 𝒮.Et v →ₐ[𝓞] Lv) (ιv : 𝒮.Et v →ₐ[𝓞] Lv) (c₂ v j)))
          (Φ.toPowerSeries j)) t ∈ (Ideal.span {(p : Lv ⊗[𝓞] Lv)}).radical := by
      rintro (j | j)
      · exact map_mem_radical_of_mem_radical
          (Algebra.TensorProduct.includeLeft : Lv →ₐ[𝓞] Lv ⊗[𝓞] Lv) p (hΨrad j)
      · exact MvFormalGroup.adicEval_mem_radical _ hin (Φ.constantCoeff_eq_zero j)
    rw [AlgHom.convMul_apply]
    change Algebra.TensorProduct.lift Q Q' (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝓞) (Ψv (X j))) = _
    rw [hcomul j, MvFormalGroup.map_adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)}) (Ideal.span {(p : Lv)})
      (Algebra.TensorProduct.lift Q Q' (fun _ _ => Commute.all _ _)) (span_natCast_fg p)
      (map_mem_radical_span_natCast _ p) hout]
    congr 1
    funext t
    rcases t with j | j
    · simp only [Sum.elim_inl]
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · simp only [Sum.elim_inr]
      rw [MvFormalGroup.map_adicEval (Ideal.span {(p : Lv ⊗[𝓞] Lv)}) (Ideal.span {(p : Lv)})
        (Algebra.TensorProduct.lift Q Q' (fun _ _ => Commute.all _ _)) (span_natCast_fg p)
        (map_mem_radical_span_natCast _ p) hin]
      congr 1
      funext t'
      rcases t' with j' | j'
      · simp only [Sum.elim_inl]
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      · simp only [Sum.elim_inr]
        exact lift_map_apply Q Q' _ _ (c₂ v j')

  have hconv_y : ∀ (Q Q' : Lv →ₐ[𝓞] Lv) (t : 𝒮.Et v),
      ((WithConv.toConv Q * WithConv.toConv Q').ofConv.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) t =
        ((Algebra.TensorProduct.lift (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (Q'.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
          (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) t := by
    intro Q Q' t
    rw [AlgHom.comp_apply, AlgHom.convMul_apply, AlgHom.comp_apply]
    change Algebra.TensorProduct.lift Q Q' (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝓞) (ιv t)) =
      Algebra.TensorProduct.lift (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (Q'.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
        (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝓞) t)
    rw [← CoalgHomClass.map_comp_comul_apply ιv t]
    generalize Coalgebra.comul (R := 𝓞) t = z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

  set ξ : (Lv →ₐ[𝓞] Lv) → Localization.Away (p : Lv) := fun Q =>
    PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun j => Q (Ψv (X j))) (𝒮.a i n)) +
      PLoc.wSeries p (fun k => (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (𝒮.ĉ i k v)) with hξ

  have hξmul : ∀ Q Q' : Lv →ₐ[𝓞] Lv, ξ (WithConv.toConv Q * WithConv.toConv Q').ofConv = ξ Q + ξ Q' := by
    intro Q Q'
    have h := hLOGA Lv hpL hLc v (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (Q'.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
      (fun j => Q (Ψv (X j))) (fun j => Q' (Ψv (X j))) (hQrad Q) (hQrad Q') i
    have e1 : (fun n => MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
        (fun j => (WithConv.toConv Q * WithConv.toConv Q').ofConv (Ψv (X j))) (𝒮.a i n)) =
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
            (Sum.elim (fun j => Q (Ψv (X j)))
              (fun i => MvFormalGroup.adicEval (Ideal.span {(p : Lv)})
                (Sum.elim (fun j => Q' (Ψv (X j)))
                  (fun j => Algebra.TensorProduct.lift (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
                    (Q'.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (fun _ _ => Commute.all _ _) (c₂ v j)))
                (Φ.toPowerSeries i))) (Φ.toPowerSeries i)) (𝒮.a i n)) := by
      funext n
      congr 1
      funext j
      exact hconv_x Q Q' j
    have e2 : (fun k => ((WithConv.toConv Q * WithConv.toConv Q').ofConv.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
        (𝒮.ĉ i k v)) = (fun k => ((Algebra.TensorProduct.lift (Q.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv))
          (Q'.comp (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (fun _ _ => Commute.all _ _)).comp
            (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (𝒮.ĉ i k v)) :=
      funext fun k => hconv_y Q Q' _
    simp only [hξ]
    rw [e1, e2]
    exact h

  have hξone : ξ ((Algebra.ofId 𝓞 Lv).comp (Bialgebra.counitAlgHom 𝓞 Lv)) = 0 := by
    have hx0 : (fun j => ((Algebra.ofId 𝓞 Lv).comp (Bialgebra.counitAlgHom 𝓞 Lv)) (Ψv (X j))) =
        fun _ => (0 : Lv) := by
      funext j
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hΨε, map_zero]
    have hy0 : (fun k => (((Algebra.ofId 𝓞 Lv).comp (Bialgebra.counitAlgHom 𝓞 Lv)).comp
        (ιv : 𝒮.Et v →ₐ[𝓞] Lv)) (𝒮.ĉ i k v)) = fun _ => (0 : Lv) := by
      funext k
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
      change algebraMap 𝓞 Lv (Coalgebra.counit (R := 𝓞) (ιv (𝒮.ĉ i k v))) = 0
      rw [CoalgHomClass.counit_comp_apply, h𝒮.counit_ĉ, map_zero]
    have ha0 : (fun n => MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun _ : Fin 𝒮.d => (0 : Lv)) (𝒮.a i n)) =
        fun _ => (0 : Lv) :=
      funext fun n => adicEval_zero_eq_zero _ (h𝒮.constantCoeff_a i n)
    simp only [hξ]
    rw [hx0, hy0, ha0, PLoc.wSeries_eq_wPartialSum_of_forall_eq_zero p hpL (N := 0) (fun _ _ => rfl),
      PLoc.wPartialSum_zero, add_zero]

  have hξn : ∀ n : ℕ, ξ (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 Lv n) = n • ξ (AlgHom.id 𝓞 Lv) := by
    intro n
    induction n with
    | zero => rw [PDivisibleGroup.Hopf.nsmulAlgHom_zero, hξone, zero_smul]
    | succ n ih => rw [PDivisibleGroup.Hopf.nsmulAlgHom_succ, hξmul, ih, succ_nsmul]
  have hξid : ξ (AlgHom.id 𝓞 Lv) = 0 := by
    have h := hξn (p ^ v)
    rw [hkill, hξone] at h
    calc ξ (AlgHom.id 𝓞 Lv)
        = (PLoc.invPow p Lv v * algebraMap Lv (Localization.Away (p : Lv)) ((p : Lv) ^ v)) *
            ξ (AlgHom.id 𝓞 Lv) := by rw [PLoc.invPow_mul_algebraMap_pow, one_mul]
      _ = PLoc.invPow p Lv v * ((p ^ v : ℕ) • ξ (AlgHom.id 𝓞 Lv)) := by
          rw [nsmul_eq_mul, mul_assoc, Nat.cast_pow, map_pow, map_natCast]
      _ = 0 := by rw [← h, mul_zero]

  set fL : 𝒮.Gc v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv :=
    (ee : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv).comp Algebra.TensorProduct.includeLeft with hfL
  set eL : 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv :=
    (ee : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv).comp Algebra.TensorProduct.includeRight with heL
  have hee : (ee : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv) =
      Algebra.TensorProduct.lift fL eL (fun _ _ => Commute.all _ _) :=
    eq_lift_comp_includeLeft_includeRight _

  have hsplit : Deformation.DieudonneModule.eval (ZMod p) p
      ((ee.comp (𝒮.Θ v) : G v →ₐc[ZMod p] ZMod p ⊗[𝓞] Lv) : G v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv)
        (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) =
      Deformation.DieudonneModule.eval (ZMod p) p fL
          (Deformation.DieudonneModule.map (ZMod p) p (𝒮.qc v) (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞))) +
        Deformation.DieudonneModule.eval (ZMod p) p eL
          (Deformation.DieudonneModule.map (ZMod p) p (𝒮.πe v) (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞))) := by
    change Deformation.DieudonneModule.eval (ZMod p) p
      ((ee : 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv).comp
        (𝒮.Θ v : G v →ₐ[ZMod p] 𝒮.Gc v ⊗[ZMod p] 𝒮.Ge v)) _ = _
    rw [hee, eval_lift_comp_eq_add p (𝒮.Θ v) (𝒮.qc v) (𝒮.πe v) (h𝒮.Θ_apply v), AddMonoidHom.add_apply,
      Deformation.DieudonneModule.eval_comp_bialgHom, Deformation.DieudonneModule.eval_comp_bialgHom]

  rw [← Deformation.DieudonneModule.toCovector_mem_wKer_iff hpL hred_ker.le hred_surj,
    Deformation.DieudonneModule.toCovector_map, ← Deformation.DieudonneModule.eval_apply]
  refine (UnipotentWittCovector.w_eq_zero_iff_mem_wKer p redL hpL hred_ker.le hred_surj _).1 ?_

  obtain ⟨n, u, hu, hcoef, hzero⟩ := h𝒮.realisation_conn v i
  obtain ⟨n', u', hu', hcoef', hzero'⟩ := h𝒮.realisation_etale v i
  set c : ℕ → Lv := fun k => MvFormalGroup.adicEval (Ideal.span {(p : Lv)}) (fun j => Ψv (X j)) (𝒮.a i k) with hc
  set c' : ℕ → Lv := fun k => ιv (𝒮.ĉ i k v) with hc'
  have hredc : ∀ k, redL (c k) = fL (𝒮.κ v (𝒮.abar i k)) := fun k => by
    rw [hc]
    simp only
    rw [← hΨeval, ← h𝒮.a_map]
    exact (heeκ (𝒮.a i k)).symm
  have hredc' : ∀ k, redL (c' k) = eL (𝒮.θe v ((1 : ZMod p) ⊗ₜ[𝓞] 𝒮.ĉ i k v)) := fun k =>
    (heeθ _).symm
  obtain ⟨N, hN⟩ := exists_forall_wSeries_sub_wPartialSum_mem_pSub p c
    (Deformation.FontaineLift.isPadicLimit_wPartialSum_adicEval p (𝒮.a i) (h𝒮.constantCoeff_a i) Lv
      (fun j => Ψv (X j)) hΨrad)
  have hc'mem : ∀ k, n' ≤ k → c' k ∈ Ideal.span {(p : Lv)} := fun k hk => by
    rw [← hred_ker, RingHom.mem_ker, hredc', hzero' k hk, map_zero]
  obtain ⟨N', hN'⟩ := exists_forall_wSeries_sub_wPartialSum_mem_pSub_of_forall_mem p c' n' hc'mem
  obtain ⟨Zc, hZc1, hZc2⟩ := exists_covector_lift p redL fL.toRingHom
    (u : TruncatedWittVector p n (𝒮.Gc v)) c
    (fun k hk => by rw [hredc, hcoef k hk]; rfl) (fun k hk => by rw [hredc, hzero k hk, map_zero]) N
  obtain ⟨Ze, hZe1, hZe2⟩ := exists_covector_lift p redL eL.toRingHom
    (u' : TruncatedWittVector p n' (𝒮.Ge v)) c'
    (fun k hk => by rw [hredc', hcoef' k hk]; rfl) (fun k hk => by rw [hredc', hzero' k hk, map_zero]) N'
  have hZ : UnipotentWittCovector.map p redL (Zc + Ze) =
      Deformation.DieudonneModule.eval (ZMod p) p
        ((ee.comp (𝒮.Θ v) : G v →ₐc[ZMod p] ZMod p ⊗[𝓞] Lv) : G v →ₐ[ZMod p] ZMod p ⊗[𝓞] Lv)
        (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) := by
    rw [map_add, hZc1, hZe1, hsplit, ← hu, ← hu', Deformation.DieudonneModule.eval_of,
      Deformation.DieudonneModule.eval_of]
  rw [← hZ, UnipotentWittCovector.w_map p redL hred_ker.le, Submodule.Quotient.mk_eq_zero, map_add, hZc2, hZe2]

  have hξid' : PLoc.wSeries p c + PLoc.wSeries p c' = 0 := hξid
  have e : PLoc.wPartialSum p c (n + N) + PLoc.wPartialSum p c' (n' + N') =
      -((PLoc.wSeries p c - PLoc.wPartialSum p c (n + N)) +
        (PLoc.wSeries p c' - PLoc.wPartialSum p c' (n' + N'))) + (PLoc.wSeries p c + PLoc.wSeries p c') := by
    abel
  rw [e, hξid', add_zero]
  exact neg_mem (add_mem (hN _ (Nat.le_add_left _ _)) (hN' _ (Nat.le_add_left _ _)))

end S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle
end P2MW
export P2MW.S_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle (solution)
