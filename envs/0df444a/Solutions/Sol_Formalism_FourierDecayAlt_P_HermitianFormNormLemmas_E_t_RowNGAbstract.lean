-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.t_RowNGAbstract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:17.030342+00:00
-- url     : https://prove2.me/submissions/491ce284-3a6d-45bb-ab03-51c076376633

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_E_blockMinorWeight_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_E_occ_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
theorem _root_.solution : Formalism.FourierDecayAlt.PN.RowNGAbstract := by
  intro hC hCSS hRFC hCCS hFB hSB hMA E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N C1 C0 Aexp
    Pc gf cSt AAre e1 TB hexp hPc hgf hcSt hAA he1 hAbs hClass hAmp hNorm hPts hLoc hMeas hGen hHt hTB
  obtain ⟨hStep4, hOm, hWCS, hE5⟩ := hC
  obtain ⟨hsum, heq⟩ := hRFC hCSS τ Rw I H H₁ X E r Cl Nu N hAbs hClass
  rw [heq]
  have hG : 0 < X.Gam1 := hAbs.2.2
  apply mul_le_mul_of_nonneg_left _ hG.le
  apply hsum.tsum_le_of_sum_le
  intro Cs
  have hW : ∀ γ, IsPt X N γ → 0 < Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * (Pc * N.NG γ ^ 6) := by
    intro γ hγ
    have h1 := (hHt γ hγ).1
    have := blockMinorWeight_pos γ
    positivity
  refine hCCS hWCS Cl (Pts E r × Nu) H₁ (fun c x => grp X N c x.1 x.2)
    (fun x => Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight x.1 * (Pc * N.NG x.1 ^ 6))
    (fun c x => N.a2 c x.1 x.2 * N.J2loc x.1) _ _ (by positivity) ?_ ?_ ?_ ?_ Cs
  · intro c j hj
    exact hW j.1 ⟨c, j.2, occ_of_ne X N c j.1 j.2 hj⟩
  · intro c j
    exact hAmp.2.2 c j.1 j.2
  · intro c T hT
    refine hFB (Pts E r) Nu Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (fun γ => Pc * N.NG γ ^ 6) (Occ X N c) _
      (fun γ => blockMinorWeight_pos γ) ?_ ?_ ?_ T (fun x hx => occ_of_ne X N c x.1 x.2 (hT x hx))
    · intro γ ν hο
      have h1 := (hHt γ ⟨c, ν, hο⟩).1
      positivity
    · intro γ S hS
      exact hNorm c γ S hS
    · intro S hS
      refine hE5 E r S (fun γ hγ => ?_)
      obtain ⟨ν, hν⟩ := hS γ hγ
      exact hPts γ ⟨c, ν, hν⟩
  · intro T hT
    refine hSB Cl (Pts E r) Nu (IsPt X N) N.a2 Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight N.J2loc N.jacobianSquareBound N.n N.NG N.ND N.Hh N.ngen
      (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹) cSt AAre e1 gf Pc TB (e7 C1 C0 r) (eN r) Aexp
      (by positivity) hcSt hAA he1 hgf hPc.le hexp hAmp.1 ?_ ?_ ?_ ?_ ?_ hTB T ?_
    · intro γ hγ
      obtain ⟨L, hB, _, _, _, _, hH, _⟩ := hLoc γ hγ ∅
      refine ⟨blockMinorWeight_pos γ, hAmp.2.1 γ, (hMeas γ hγ).1, (hGen γ hγ).1, (hHt γ hγ).1, (hHt γ hγ).2.1, ?_⟩
      rw [hH]
      unfold LocalNG.Htot
      exact Finset.prod_induction _ (fun x => 1 ≤ x)
        (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun p _ => hB.2.1 p)
    · intro γ hγ S
      obtain ⟨L, hB, hNG, hMR, hU, ha, hH, hn⟩ := hLoc γ hγ S
      have := hMA hStep4 hOm Cl Nu L C1 C0 r k hB hNG hMR hU S
      rw [Finset.sum_congr rfl ha, hH, hn]
      exact this
    · intro γ hγ; exact (hMeas γ hγ).2
    · intro γ hγ; exact (hGen γ hγ).2
    · intro γ hγ; exact (hHt γ hγ).2.2
    · intro x hx
      exact ⟨x.1, x.2.2, occ_of_ne X N x.1 x.2.1 x.2.2 (hT x hx)⟩
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
