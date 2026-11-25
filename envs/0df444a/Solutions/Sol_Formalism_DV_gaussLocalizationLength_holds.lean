-- Prove2me | solution 1 for Formalism.DV.gaussLocalizationLength_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:20.842949+00:00
-- url     : https://prove2.me/submissions/74607aa3-47c1-4533-91d0-83cd47599e8c

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
import Theorems.Thm_Formalism_DV_GaussP_length_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial IsLocalRing
noncomputable section
namespace Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)
end GaussP
private theorem length_tensor_eq_length_of_simple_length_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.FaithfullyFlat O A]
    (hk : ∀ (S : Type) [AddCommGroup S] [Module O S], IsSimpleModule O S →
      Module.length A (TensorProduct O A S) = 1)
    (N : Type) [AddCommGroup N] [Module O N] :
    Module.length A (TensorProduct O A N) = Module.length O N := by
  have fin : ∀ (M : Type) [AddCommGroup M] [Module O M], IsFiniteLength O M →
      Module.length A (TensorProduct O A M) = Module.length O M := by
    intro M _ _ hM
    induction hM with
    | @of_subsingleton M _ _ _ =>
      have h0 : Subsingleton (TensorProduct O A M) := by
        refine subsingleton_of_forall_eq 0 (fun x => ?_)
        induction x using TensorProduct.induction_on with
        | zero => rfl
        | tmul a n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      have h1 : Module.length O M = 0 := Module.length_eq_zero_iff.2 inferInstance
      have h2 : Module.length A (TensorProduct O A M) = 0 := Module.length_eq_zero_iff.2 h0
      rw [h1, h2]
    | @of_simple_quotient M _ _ K _ _ ih =>
      have hf : Function.Injective K.subtype := fun a b h => Subtype.ext h
      have hg : Function.Surjective K.mkQ := by
        first
          | exact Submodule.mkQ_surjective K
          | exact Submodule.Quotient.mk_surjective K
      have hfg : Function.Exact K.subtype K.mkQ := LinearMap.exact_subtype_mkQ K
      have hf' : Function.Injective (K.subtype.baseChange A) := by
        first
          | exact Module.Flat.lTensor_preserves_injective_linearMap _ hf
          | exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) _ hf
          | (rw [LinearMap.baseChange_eq_ltensor]; exact Module.Flat.lTensor_preserves_injective_linearMap _ hf)
      have hg' : Function.Surjective (K.mkQ.baseChange A) := by
        first
          | exact LinearMap.lTensor_surjective A hg
          | exact LinearMap.lTensor_surjective _ hg
          | (rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective A hg)
      have hfg' : Function.Exact (K.subtype.baseChange A) (K.mkQ.baseChange A) := by
        first
          | exact lTensor_exact A hfg hg
          | exact lTensor_exact (Q := A) hfg hg
          | exact lTensor_exact hfg hg
          | (rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]; exact lTensor_exact A hfg hg)
      have h1 : Module.length O (M ⧸ K) = 1 := Module.length_eq_one_iff.2 inferInstance
      rw [Module.length_eq_add_of_exact _ _ hf hg hfg,
        Module.length_eq_add_of_exact _ _ hf' hg' hfg', ih, hk (M ⧸ K) inferInstance, h1]
  have mono : ∀ P Q : Submodule O N, P ≤ Q →
      LinearMap.range (P.subtype.baseChange A) ≤ LinearMap.range (Q.subtype.baseChange A) := by
    intro P Q h
    have e : P.subtype = Q.subtype.comp (Submodule.inclusion h) := LinearMap.ext fun _ => rfl
    rw [e, LinearMap.baseChange_comp]
    exact LinearMap.range_comp_le_range _ _
  have key : ∀ P Q : Submodule O N,
      LinearMap.range (Q.subtype.baseChange A) ≤ LinearMap.range (P.subtype.baseChange A) → Q ≤ P := by
    intro P Q h
    have hz : P.mkQ.comp P.subtype = 0 :=
      LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero P).2 x.2
    have hg0 : LinearMap.lTensor A (P.mkQ.comp Q.subtype) = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, hy⟩ :=
        LinearMap.mem_range.1 (h (LinearMap.mem_range_self (Q.subtype.baseChange A) x))
      rw [LinearMap.zero_apply, LinearMap.lTensor_comp, LinearMap.comp_apply]
      change (P.mkQ.baseChange A) ((Q.subtype.baseChange A) x) = 0
      rw [← hy]
      first
        | rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz, LinearMap.baseChange_zero,
            LinearMap.zero_apply]
        | simp [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz]
    have hg : P.mkQ.comp Q.subtype = 0 := (Module.FaithfullyFlat.zero_iff_lTensor_zero O A _).2 hg0
    intro n hn
    have h2 : (Submodule.Quotient.mk n : N ⧸ P) = 0 := LinearMap.congr_fun hg ⟨n, hn⟩
    exact (Submodule.Quotient.mk_eq_zero P).1 h2
  have sm : StrictMono (fun P : Submodule O N => LinearMap.range (P.subtype.baseChange A)) := by
    intro P Q hPQ
    exact (mono P Q hPQ.le).lt_of_ne fun h => hPQ.ne (le_antisymm hPQ.le (key P Q h.ge))
  have ineq : Module.length O N ≤ Module.length A (TensorProduct O A N) := by
    have h3 := Order.krullDim_le_of_strictMono _ sm
    rw [← Module.coe_length, ← Module.coe_length] at h3
    exact_mod_cast h3
  by_cases hN : Module.length O N = ⊤
  · rw [hN] at ineq
    rw [hN]
    exact top_le_iff.1 ineq
  · exact fin N (Module.length_ne_top_iff.1 hN)
end Formalism.DV
end
end

set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism.DV
namespace Formalism.DV
theorem _root_.solution : GaussLength := by
  intro σ O _ _ _ _ _ N _ _
  haveI : Module.FaithfullyFlat O (Localization.AtPrime (gaussIdeal σ O)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine length_tensor_eq_length_of_simple_length_one ?_ N
  intro S _ _ hS
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hS
  have hIm : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  have e1 := LinearEquiv.length_eq (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (Localization.AtPrime (gaussIdeal σ O)) (Localization.AtPrime (gaussIdeal σ O))) e)
  have e2 := LinearEquiv.length_eq (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (Localization.AtPrime (gaussIdeal σ O)) (IsLocalRing.maximalIdeal O)).toLinearEquiv
  exact e1.trans (e2.symm.trans (GaussP.length_residue σ O))
end Formalism.DV
