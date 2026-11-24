-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:12.354692+00:00
-- url     : https://prove2.me/submissions/110eb6f8-5605-482b-8c33-acf1cef6dc56

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_apply

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} :
    F.offMat x y ≠ 0 ↔
      F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 ∧ gram F.ind x y ≠ 0 := by
  rw [F.offMat_apply]
  split_ifs with h
  · exact ⟨fun hg ↦ ⟨h.1, h.2, hg⟩, fun hg ↦ hg.2.2⟩
  · exact ⟨fun hg ↦ absurd rfl hg, fun hg ↦ absurd ⟨hg.1, hg.2.1⟩ h⟩
end BSLambda.CertFamily
