-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:23:21.025091+00:00
-- url     : https://prove2.me/submissions/b6a778bc-d21c-418c-8a29-03cf24150b01

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum
import Theorems.Thm_Formalism_L2_Col_LocOp_conj_eq_zero_iff
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_count_of_orbits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (A : LocOp S S') (B : LocOp S' S) (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (hB : ∀ g, B.tr g = e g)
    (hsupp : ∀ d d', A.ker d' d = 0 ↔ B.ker d d' = 0)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' (A.app φ) ψ = S.ipOf h s φ (B.app ψ) := by
  classical
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  let act : MulAction S.G S'.D := MulAction.compHom S'.D (e : S.G →* S'.G)
  have hact : ∀ (γ : S.G) (b : S'.D), γ • b = e γ • b := fun _ _ => rfl
  have hstab : ∀ b : S'.D, (MulAction.stabilizer S.G b) ≃ (MulAction.stabilizer S'.G b) := fun b =>
    Equiv.subtypeEquiv e.toEquiv fun γ => Iff.rfl
  have hinj : Function.Injective s.rep := fun c c' hc => by rw [← s.spec c, hc, s.spec]
  have hinj' : Function.Injective s'.rep := fun c c' hc => by rw [← s'.spec c, hc, s'.spec]
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits S.G S.D S'.D K
    (fun a => (B.ker a).support) (fun b => (A.ker b).support)
    (fun a b => S.pair ((φ : S.D → S.V) a) (B.ker a b ((ψ : S'.D → S'.V) b)))
    (Finset.univ.image s.rep) (Finset.univ.image s'.rep)
    (by
      intro a b
      rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, not_iff_not]
      exact (hsupp a b).symm)
    (by
      intro γ a b hb
      rw [Finsupp.mem_support_iff] at hb ⊢
      rw [hact, ← hB, B.equiv, Ne, conj_eq_zero_iff]
      exact hb)
    (by
      intro γ a b _
      show S.pair ((φ : S.D → S.V) (γ • a)) (B.ker (γ • a) (γ • b) ((ψ : S'.D → S'.V) (γ • b))) = _
      rw [hact, ← hB, B.equiv, φ.2, ψ.2]
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply (S'.ρ (B.tr γ)⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        h.inv])
    h.fin_stab
    (by
      intro b
      have := h'.fin_stab b
      exact Finite.of_equiv _ (hstab b).symm)
    (by
      intro a
      refine ⟨s.rep (S.cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact (S.cls_eq_iff _ _).mp (s.spec _)
      · rintro r ⟨hr, hr2⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : S.cls (s.rep c) = S.cls a := (S.cls_eq_iff _ _).mpr hr2
        rw [← h1, s.spec])
    (by
      intro b
      refine ⟨s'.rep (S'.cls b), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
      · obtain ⟨g', hg'⟩ := (S'.cls_eq_iff _ _).mp (s'.spec (S'.cls b))
        exact ⟨e.symm g', by show e (e.symm g') • b = _; rw [MulEquiv.apply_symm_apply, hg']⟩
      · rintro r ⟨hr, γ, hγ⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
        have h1 : S'.cls (s'.rep c) = S'.cls b := (S'.cls_eq_iff _ _).mpr ⟨e γ, hγ⟩
        rw [← h1, s'.spec])
  rw [Finset.sum_image (fun c _ c' _ hc => hinj hc), Finset.sum_image (fun c _ c' _ hc => hinj' hc)] at key
  rw [GSD.ipOf_eq_sum, GSD.ipOf_eq_sum]
  refine Eq.trans ?_ (key.symm.trans ?_)
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Nat.card_congr (hstab (s'.rep c')), Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
    congr 1
    unfold app
    rw [Finsupp.sum, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun d _ => hadj _ _ _ _
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
    congr 1
    unfold app
    rw [Finsupp.sum, map_sum]
end Formalism.L2.Col.LocOp
