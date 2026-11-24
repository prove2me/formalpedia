-- Prove2me | solution 1 for Formalism.L2.NT.hasLabelO_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:28.665929+00:00
-- url     : https://prove2.me/submissions/1d0f20b4-fcb0-42b5-9b06-a31611b13c85

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Theorems.Thm_Formalism_L2_NT_coeff_zero_ne_of_monic_irr
import Theorems.Thm_Formalism_L2_PT_simple_transp
import Theorems.Thm_Formalism_L2_PT_isCuspidal_transp
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.PT
variable {g : ℕ} [Fact g.Prime]
namespace Formalism.L2.NT
theorem _root_.solution {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) {r : ℕ}
    {τ : FDRep ℂ (GL (Fin r) (ZMod g))} {f : (ZMod g)[X]} (h : HasLabelO O τ f) :
    f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨s, b, lam, hb, hlam, -, rfl⟩ := h
  have hfac : ∀ c, (labO O (lam c)).Monic ∧ Irreducible (labO O (lam c)) ∧ labO O (lam c) ≠ X ∧
      (labO O (lam c)).natDegree = Fintype.card {i // b i = c} := by
    intro c
    obtain ⟨i, hi⟩ := hb c
    have hpos : 1 ≤ Fintype.card {i // b i = c} := Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    exact O.lab_spec _ _ hpos (simple_transp _ (hlam c).1) (isCuspidal_transp _ (hlam c).2)
  have hmon : ∀ c ∈ (Finset.univ : Finset (Fin s)), (labO O (lam c)).Monic := fun c _ => (hfac c).1
  refine ⟨monic_prod_of_monic _ _ hmon, ?_, ?_⟩
  · rw [natDegree_prod_of_monic _ _ hmon, Finset.sum_congr rfl (fun c _ => (hfac c).2.2.2)]
    first
      | (rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin])
      | (simp only [Fintype.card_subtype]
         rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (b x)), Finset.card_univ,
           Fintype.card_fin])
      | (simp only [Fintype.card_subtype]
         rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (b x))]
         simp)
  · rw [coeff_zero_eq_eval_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [← coeff_zero_eq_eval_zero]
    exact coeff_zero_ne_of_monic_irr (hfac c).1 (hfac c).2.1 (hfac c).2.2.1
end Formalism.L2.NT
