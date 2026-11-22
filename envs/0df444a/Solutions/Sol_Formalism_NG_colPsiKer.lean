-- Prove2me | solution 1 for Formalism.NG.colPsiKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:05.08644+00:00
-- url     : https://prove2.me/submissions/8899eb20-a1c3-42a7-87a3-cb23cd6e1a40

import Definitions.Def_Formalism_CharacterColumnKernels_StatementPsi
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatColPsiKer := by
  intro O A T' G _ _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0
  ext φ
  simp only [LinearMap.mem_ker, kerY, Submodule.mem_iInf]
  constructor
  · intro h
    have hg : ∀ g, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0 := fun g => by
      have := congrArg (fun c : coZ1s (uRep O (M := M) r χ) => (c : G → M) g) h
      exact this
    have key : ∀ (x : A) (hx : x ∈ Submodule.span A (Set.range (ycoc r χ E))),
        φ (Submodule.Quotient.mk (((⟨x, hx⟩ : Ymod r χ E)),
          (0 : (l : ι) → A × (Fin (j l) → A) × A))) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact hg g
      | zero =>
        show φ (Submodule.Quotient.mk 0) = 0
        rw [Submodule.Quotient.mk_zero, map_zero]
      | add x z hx hz ihx ihz =>
        have e : (((⟨x + z, Submodule.add_mem _ hx hz⟩ : Ymod r χ E)),
            (0 : (l : ι) → A × (Fin (j l) → A) × A)) =
            (((⟨x, hx⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) +
            (((⟨z, hz⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) :=
          Prod.ext rfl (add_zero 0).symm
        rw [e, Submodule.Quotient.mk_add, map_add, ihx, ihz, add_zero]
      | smul a x hx ih =>
        have e : (((⟨a • x, Submodule.smul_mem _ a hx⟩ : Ymod r χ E)),
            (0 : (l : ι) → A × (Fin (j l) → A) × A)) =
            a • (((⟨x, hx⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) :=
          Prod.ext rfl (smul_zero a).symm
        rw [e, Submodule.Quotient.mk_smul, map_smul, ih, smul_zero]
    intro y
    exact key y.1 y.2
  · intro h
    apply Subtype.ext
    funext g
    exact h ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩
end Formalism.NG
