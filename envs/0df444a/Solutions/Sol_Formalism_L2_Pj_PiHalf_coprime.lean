-- Prove2me | solution 1 for Formalism.L2.Pj.PiHalf.coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:34.161782+00:00
-- url     : https://prove2.me/submissions/0d966ef9-4963-4294-81d8-ffadf6e212f0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DepthPins

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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace Formalism.L2.Pj
namespace PiHalf
theorem _root_.solution {l : Level H} {D : DepData E} (h : PiHalf l D) (i k : Fin 2) :
    IsCoprime (D.pi i) (H.bar (D.pi k)) := by
  have hd : ∀ j : Fin 2, D.pi j ∣ D.pi 0 * D.pi 1 := fun j =>
    match j with
    | 0 => dvd_mul_right _ _
    | 1 => dvd_mul_left _ _
  have h1 : l.Mb ≤ Ideal.span {D.pi i} := by
    rw [← h]; exact Ideal.span_singleton_le_span_singleton.2 (hd i)
  have h2 : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Ideal.span {H.bar (D.pi k)} := by
    rw [← h, Ideal.map_span, Set.image_singleton]
    exact Ideal.span_singleton_le_span_singleton.2 (map_dvd (H.bar : 𝓞 E →+* 𝓞 E) (hd k))
  have htop : Ideal.span {D.pi i} ⊔ Ideal.span {H.bar (D.pi k)} = ⊤ := by
    rw [eq_top_iff, ← l.coprime]; exact sup_le_sup h1 h2
  exact (Ideal.isCoprime_span_singleton_iff _ _).1 (Ideal.isCoprime_iff_sup_eq.2 htop)
end PiHalf
end Formalism.L2.Pj
