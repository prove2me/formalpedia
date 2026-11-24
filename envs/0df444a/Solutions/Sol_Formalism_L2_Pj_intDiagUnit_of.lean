-- Prove2me | solution 1 for Formalism.L2.Pj.intDiagUnit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:01.481095+00:00
-- url     : https://prove2.me/submissions/34912dff-f9d8-42c6-975c-5214f071780f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Theorems.Thm_Formalism_L2_Pj_valV_algebraMap_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution (hL : IntLatU Xo c) : IntDiagUnit Xo c := by
  intro T io y y' t hb k
  let := io.toAlgebra
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hb
  obtain ⟨hA, hG⟩ := (show IntLatU Xo c from hL) T io y y' hx
  rcases k with _ | ⟨τ, i⟩
  · exact hG (t none) pm h1 h2 h3
  obtain ⟨A, hdet, hAc⟩ := hA τ

  have hrow : ∀ i', ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i' = (t (some ⟨τ, i'⟩) : T.Fr) ∧
      (∀ j, i' < j → cf j = 0) ∧ ∀ j, algebraMap T.V T.Fr (A i' j) = cf j := by
    intro i'
    obtain ⟨cf, hci, hcz, hcomb⟩ := hu τ i'
    have htan : IsTanAt y.1.x (y'.1.u τ i') := hx ▸ y'.1.tan τ i'
    obtain ⟨a0, -, huniq⟩ := y.1.basis τ (y'.1.u τ i') htan (y'.1.eig τ i')
    have e1 := huniq cf hcomb
    have e2 := huniq _ (hAc i')
    exact ⟨cf, hci, hcz, fun j => congrFun (e2.trans e1.symm) j⟩
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hlow : A.IsLowerTriangular := by
    intro i' j hij
    obtain ⟨cf, -, hcz, hA'⟩ := hrow i'
    apply hinj
    rw [hA' j, hcz j hij, map_zero]
  rw [Matrix.det_of_isLowerTriangular A hlow, IsUnit.prod_univ_iff] at hdet
  obtain ⟨cf, hci, -, hA'⟩ := hrow i
  rw [← hci, ← hA' i]
  exact valV_algebraMap_unit T (hdet i)
end Formalism.L2.Pj
