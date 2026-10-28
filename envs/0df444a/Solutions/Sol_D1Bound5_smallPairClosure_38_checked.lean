-- Prove2me | solution 1 for D1Bound5.smallPairClosure_38_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:35:30.185979+00:00
-- url     : https://prove2.me/submissions/38338a07-5865-4a97-b109-32f195db9983

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
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_004
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_006
import Theorems.Thm_D1Bound5_PairGraphPrepared38_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
/- Preserved body from D1Bound5.SmallPairGraphInputs38; original SHA256 e84905f2c584eaec762f49ff95cacb67eda33b4f26e2c70c9b7b8b2cce33bac3. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared38



end PairGraphPrepared38
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic38; original SHA256 dd8dbfa6abf4d50ab024f61aee47d820a823b926c36e406836f87c60656daee7. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData38; original SHA256 c6164df96db4aa1be0a86091c70be1a406e41f83d72c88d46eabb3e7189c3052. -/

namespace D1Bound5.PairGraphPrepared38
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared38

/- Preserved body from D1Bound5.SmallPairGraphClosure38; original SHA256 b10bc5b53ff5864b17af0b52e70793fe0d0cc33ca5726ae8e59895847f319d29. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared38



theorem _root_.solution :
    pairClosureBool smallPairA_38 smallPairB_38
      (10^1100) smallPairClosure_38 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_38 smallPairB_38 anchorRoot
    (10^1100) smallPairClosure_38 witnesses destinations PairGraphPrepared38.indexed_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData38; original SHA256 bc91510fcbc172095a6e7f20939407122422a55cd73446afa31e0b04776daec7. -/

namespace D1Bound5.PairSelectedPrepared38
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared38

/- Preserved body from D1Bound5.SmallPairLightAssembly38; original SHA256 0a6d4a5a2f8cf5b522f0c22f64572b8fe8962d975aa36145b357f51474e4371c. -/

namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared38

/- Preserved body from D1Bound5.SmallPairGraphTriangle38; original SHA256 cb5933e1c0e765de3430434a98639be128637fe79d2d295f12b7f83e963f8872. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData38; original SHA256 83f2c3bd68777968da247a58362b3e2051ce156b248c76a29c29eb55c1278ea0. -/
end
