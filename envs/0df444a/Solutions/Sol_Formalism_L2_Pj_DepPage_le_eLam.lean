-- Prove2me | solution 1 for Formalism.L2.Pj.DepPage.le_eLam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:57.724794+00:00
-- url     : https://prove2.me/submissions/09e7ff91-46d5-4b02-8563-16928d821c7b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Copies
variable {R : Type} [CommRing R] {d : ℕ}
end Copies
section Loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable [StarRing (𝓞 E)]
variable (Xo c)
end Loc
section Num
namespace DepPage
variable (Q : DepPage)
end DepPage
end Num
section Places
variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra (𝓞 K) (𝓞 L)] [Algebra.IsIntegral (𝓞 K) (𝓞 L)]
end Places
private lemma le_ceil_toNat_lemma (a x b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * x ≤ ((⌈a * (x + b)⌉.toNat : ℕ) : ℝ) := by
  have h1 : a * x ≤ a * (x + b) := mul_le_mul_of_nonneg_left (by linarith) ha
  have h2 : a * (x + b) ≤ (⌈a * (x + b)⌉ : ℝ) := Int.le_ceil _
  have h3 : ((⌈a * (x + b)⌉ : ℤ) : ℝ) ≤ ((⌈a * (x + b)⌉.toNat : ℕ) : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  linarith
section Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
variable {Xo c}
variable {LL : Type} [Field LL] [NumberField LL] [Algebra (𝓞 c.F) (𝓞 LL)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 LL)]
variable [Algebra (𝓞 E) LL]
end Inst
section Props
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
variable {Xo c}
end Props
end Formalism.L2.Pj
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace Formalism.L2.Pj
namespace DepPage
theorem _root_.solution (Q : DepPage) (eL : ℕ) (nu : ℝ) (p : ℕ) :
    (eL : ℝ) * (Q.T : ℝ) * nu ≤ (Q.eLam eL nu p : ℝ) := by
  unfold DepPage.eLam
  refine le_ceil_toNat_lemma _ _ _ (by positivity) ?_
  split_ifs <;> norm_num
end DepPage
end Formalism.L2.Pj
