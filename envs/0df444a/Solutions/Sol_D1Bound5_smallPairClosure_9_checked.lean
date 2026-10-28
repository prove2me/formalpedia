-- Prove2me | solution 1 for D1Bound5.smallPairClosure_9_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:06:05.128979+00:00
-- url     : https://prove2.me/submissions/7ead5bef-c620-445c-8f9f-871c37600174

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData9_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData9_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared9_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
/- Preserved body from D1Bound5.SmallPairGraphInputs9; original SHA256 ca62ac88f6fd92ac6c88d32728f23d50acccc1b3de5275a1968707cf69b7dac7. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared9



end PairGraphPrepared9
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic9; original SHA256 fd1d6157d4b4c24fef10d7a2f6237fde1f8cbfff05503e9ebe391e7d05838373. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData9; original SHA256 31c1f2f98508bd3fc8b92151463182de4b1512598a59fc695daddafd280d08b6. -/

namespace D1Bound5.PairGraphPrepared9
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared9

/- Preserved body from D1Bound5.SmallPairGraphClosure9; original SHA256 e94a9445b1c122ab641e2de2725cc3f01edac2e0681257f16ef8978a3df72c9f. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared9



theorem _root_.solution :
    pairClosureBool smallPairA_9 smallPairB_9
      (10^1100) smallPairClosure_9 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_9 smallPairB_9 anchorRoot
    (10^1100) smallPairClosure_9 witnesses destinations PairGraphPrepared9.indexed_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData9; original SHA256 6ff0a988a5e6bb648adc3744b2c10ae4709041786930eb7d4d3741248612b9dd. -/

namespace D1Bound5.PairSelectedPrepared9
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared9

/- Preserved body from D1Bound5.SmallPairLightAssembly9; original SHA256 029f3dcd6a8d5e1b506a7a8bb9e59164af150af72be69790c07a5a73b8286188. -/

namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared9

/- Preserved body from D1Bound5.SmallPairGraphTriangle9; original SHA256 deaa2af82bd08f97e72491cf75a6a53a63954646129242a9f94f3c14c6e41dc1. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData9; original SHA256 88b329ddf09044b819e713be36bebaa67a0cb6ecc5714f24b166e8a129e33139. -/
end
