-- Prove2me | solution 1 for D1Bound5.PairLightPrepared2.right_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:34:29.574815+00:00
-- url     : https://prove2.me/submissions/0311674e-ab1b-4c01-9d27-0c311d9b36c3

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData2_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData2_Definitions_005
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared2_rightVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared2_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared2_right_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared2_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared2_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem right_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 0 1 sieve
      rightVertices rightCached rightRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨right_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨right_signatures_checked, right_independent_checked⟩⟩

end D1Bound5.PairLightPrepared2
end

section
/- Preserved body from D1Bound5.SmallPairGraphInputs2; original SHA256 05c6eac538f8497cd3a821770526ca8706d00a25abdc81b4c26cfd4d1fb29b57. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared2



end PairGraphPrepared2
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic2; original SHA256 26154516f673902cc1e3bce80054f0c96e08d80a543d1e1f2882f177302acaf7. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData2; original SHA256 f319a0bdaefa48f1a9f3ae5ceb65656c94c041b0fa290e14cab6856d8341c7fb. -/

namespace D1Bound5.PairGraphPrepared2
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared2

/- Preserved body from D1Bound5.SmallPairGraphClosure2; original SHA256 6c3d39e00759e54ecfe739fe7c0b0c438ed702899f4932797158545d8d3f914b. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared2





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData2; original SHA256 bd14d335ba3742940ee6255966b2aa93923682ac39e18375e9a9ee7870d1dc4f. -/

namespace D1Bound5.PairSelectedPrepared2
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared2

/- Preserved body from D1Bound5.SmallPairLightAssembly2; original SHA256 28e25096d2fda97cfe2f853e3f3dc8734674d85d678e091170cdd16eaf988ed7. -/

namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0













theorem rightCached_eq :
    rightCached = PairSelectedPrepared2.rightCached.map pairLightCachedCoordinates := by
  rfl

theorem rightRows_eq : rightRows = PairSelectedPrepared2.rightRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_2 PairGraphPrepared2.colors).2 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_0_1
    (pairSplitByMask smallPairLarge_2 PairGraphPrepared2.colors).2 PairSelectedPrepared2.rightCached PairSelectedPrepared2.rightRows
  rw [← sieve_eq, ← rightVertices_eq, ← rightCached_eq, ← rightRows_eq]
  exact right_certificate_checked

end D1Bound5.PairLightPrepared2

/- Preserved body from D1Bound5.SmallPairGraphTriangle2; original SHA256 304600336a461f07462df8aa2968c65908970f7e5cd79d6981f86853f6ac6e7d. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData2; original SHA256 89e5d1cc4246d5ec20132684b3f2d13a6ac263401e770195eef0c09fa478e927. -/
end
