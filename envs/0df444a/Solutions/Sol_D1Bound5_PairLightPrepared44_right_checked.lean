-- Prove2me | solution 1 for D1Bound5.PairLightPrepared44.right_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:04.139896+00:00
-- url     : https://prove2.me/submissions/a77ed6f6-2639-486d-8ba8-84d9838cc59f

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
import Definitions.Def_D1Bound5_SmallPairGraphData44_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData44_Definitions_005
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_4_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared44_rightVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared44_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared44_right_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared44_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared44_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem right_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 1 4 sieve
      rightVertices rightCached rightRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨right_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨right_signatures_checked, right_independent_checked⟩⟩

end D1Bound5.PairLightPrepared44
end

section
/- Preserved body from D1Bound5.SmallPairGraphInputs44; original SHA256 b443d2cf11af364c9d9082712786db2cf3a153851a5eaea7bdbb30c84d99fec0. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared44



end PairGraphPrepared44
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic44; original SHA256 f6bdb5a40012c0b78d1ce6330b64244084b8e6a6e3c41c9a3690017b0eb6f558. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData44; original SHA256 f3c4a787d1e9f9d4f74a295674b17167e04ca7bbd68b05e1aafe83388608421d. -/

namespace D1Bound5.PairGraphPrepared44
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared44

/- Preserved body from D1Bound5.SmallPairGraphClosure44; original SHA256 4dfcf91b3104c4a07c5f9491b4956fa7d08ee63ada7f4c55131fc45e109a31eb. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared44





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData44; original SHA256 6f4738d9d44c74a5377009120c16bff87092df004b921c6c5d7740d606704914. -/

namespace D1Bound5.PairSelectedPrepared44
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared44

/- Preserved body from D1Bound5.SmallPairLightAssembly44; original SHA256 72a386daf4c4fbc03e4bc740cfffed37a9495da0a7c0832f363d927056f2fbd1. -/

namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0













theorem rightCached_eq :
    rightCached = PairSelectedPrepared44.rightCached.map pairLightCachedCoordinates := by
  rfl

theorem rightRows_eq : rightRows = PairSelectedPrepared44.rightRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_1_4 (pairSplitByMask smallPairLarge_44 PairGraphPrepared44.colors).2 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_1_4
    (pairSplitByMask smallPairLarge_44 PairGraphPrepared44.colors).2 PairSelectedPrepared44.rightCached PairSelectedPrepared44.rightRows
  rw [← sieve_eq, ← rightVertices_eq, ← rightCached_eq, ← rightRows_eq]
  exact right_certificate_checked

end D1Bound5.PairLightPrepared44

/- Preserved body from D1Bound5.SmallPairGraphTriangle44; original SHA256 b0b577b7778dee384454132602d0d9a1898801dd28bbf0a19bb7e4a67095b933. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData44; original SHA256 71cc4347dc31ae756ab45cd633715fbc8dd66b09ec47b721c35b4874848ddc7a. -/
end
