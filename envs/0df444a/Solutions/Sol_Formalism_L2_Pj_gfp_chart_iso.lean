-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_chart_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:43.459538+00:00
-- url     : https://prove2.me/submissions/33d1704c-4708-42be-b2aa-0fc238884b05

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution {R : Type} [CommRing R] {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [GrpObj G₂]
    (e : G₁ ≅ G₂) [IsMonHom e.hom] {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (JetR R (Fin n) m) ⟶ G₁} (hx : IsUnivChart G₁ n xc) :
    IsUnivChart G₂ n (fun m => xc m ≫ e.hom) := by
  have h1 : ∀ X : Over (Spec (CommRingCat.of R)), (1 : X ⟶ G₁) ≫ e.hom = 1 := by
    intro X
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, hx.1 m]
  · rw [← Category.assoc, hx.2.1 m, h1]
  · intro A _ _ aug m hker y hy
    have hy' : ReciprocityTheory.ChartRestriction.G.Chart.spMap aug ≫ (y ≫ e.inv) = 1 := by
      rw [← Category.assoc, hy, ← h1, Category.assoc, e.hom_inv_id, Category.comp_id]
    obtain ⟨ψ, hψ, huniq⟩ := hx.2.2 A aug m hker (y ≫ e.inv) hy'
    refine ⟨ψ, ⟨hψ.1, ?_⟩, fun ψ' hψ' => huniq ψ' ⟨hψ'.1, ?_⟩⟩
    · rw [← Category.assoc, ← Iso.comp_inv_eq, hψ.2]
    · rw [Iso.comp_inv_eq, hψ'.2, Category.assoc]
end Formalism.L2.Pj
