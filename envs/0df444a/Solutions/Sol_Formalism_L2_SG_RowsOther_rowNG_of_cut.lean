-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.rowNG_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:28.070695+00:00
-- url     : https://prove2.me/submissions/60ff9330-3c81-4c11-9d63-02b77560310e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
import Theorems.Thm_Formalism_L2_SG_RowsOther_ngInputs_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution (hR : PN.RowNGJoint) (hC : PN.NGChain) (C1 C0 A : ℕ) (CB CSt Cg CT : ℝ)
    (h1 : 0 ≤ CB) (h2 : 0 ≤ CSt) (h3 : 0 ≤ Cg) (h4 : 0 ≤ CT) (hA : C1 + C0 + 38 ≤ A) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧
    ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
      [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r k : ℕ) (Cl Nu : Type) (N : PN.NGData τ E r Cl Nu)
      (P : Type) [Fintype P] (B : S3.MassData P) (b rd g TT cSt e1 Irat Ire : ℝ),
      X.AbsConv → X.Gam1 = B.Gam1 → PN.NormInputs B →
      PN.FrameInputs B rd g r k (Fintype.card (NumberField.InfinitePlace E)) Irat Ire →
      PN.NGSizes Cg CT CSt r (Fintype.card (NumberField.InfinitePlace E)) b rd g TT cSt e1 →
      NGFin X N k (Fintype.card (NumberField.InfinitePlace E)) C1 C0 rd g TT
        (PN.abelian₂ rd r k (Fintype.card (NumberField.InfinitePlace E)) * B.AA) e1 →
      NGReal X N (Fintype.card (NumberField.InfinitePlace E)) A CB b cSt Ire →
      X.RowNG (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
        Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card (NumberField.InfinitePlace E) : ℕ) * Real.log b))
        (B.d * B.d' / B.Dstar) := by
  obtain ⟨Cn, hCn, hmain⟩ := hR hC C1 C0 A CB CSt Cg CT h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, ?_⟩
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N P _ B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI hSz hFin hReal
  exact hmain E τ Rw I H H₁ X r k Cl Nu N P B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI hSz
    (by rw [ngInputs_iff]; exact ⟨hFin, hReal⟩)
end Formalism.L2.SG.RowsOther
