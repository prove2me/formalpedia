-- Prove2me | solution 1 for FullFormalization.foldl_bestStep_mem
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:31.154837+00:00
-- url     : https://prove2.me/submissions/f04a28b4-5f96-4141-b10d-7f39f77ed478

-- Generated from F:/20261008/FullFormalization\FullFormalization\RandomSearch.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.RandomSearch

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 21,
  strategy 4 (source line 2082): `fixed-seed random search`, and section 24
  (source lines 2177-2183):

      "固定 seed 后，random search 的 N 个查询点 q_1, ..., q_N 由 N, D 和公开采样
       规则完全确定，并且查询位置不依赖函数值。"

  Implementation semantics: `blackbox_algos.py`, `_random_search` and
  `_sample`:

      rng = random.Random(SAMPLE_SEED)           -- SAMPLE_SEED = 0
      for _ in range(spec.query_budget):
          point = (SAMPLE_STEP * rng.randint(-span, span) for each coordinate)
          answer = oracle.query(point)
          if best_value is None or answer["value"] < best_value:
              best_point, best_value = point, answer["value"]
      oracle.finish(best_point)

  with `SAMPLE_BOX = 8`, `SAMPLE_STEP = 1/2` and `span = int(SAMPLE_BOX /
  SAMPLE_STEP) = 16`.  The two facts that matter are:

  * the whole query list is fixed by the declared seed, the declared box and
    the declared step, hence by `(N, D)` alone — it does **not** depend on
    function values (source line 2183).  `q : Fin N → E` is therefore a
    parameter of this file, given before the function, and everything below is
    proved for *any* such fixed list.  This is the strict strengthening
    recorded in `DEPENDENCY_MAP.md` §9 D-2 and R11: the source uses only
    "fixed and independent of the function", and never any property of the
    concrete PRNG stream.  The seed-0 list of `blackbox_algos.py` is one
    instance.
  * the output is the **queried** point with the smallest observed value, and
    the comparison is strict (`<`), so on a tie the **earlier** query wins
    (`bestOf_pair_tie`).

  Nothing here uses the geometry of the sample box: the sample constants are
  recorded (`sampleBox`, `sampleStep`, `sampleSeed`, `sampleSpan`) because the
  frozen implementation declares them, but the theorems below hold for every
  predetermined query list.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_RandomSearch

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*}

/-! ### The declared sampler constants (frozen implementation) -/











/-! ### The best observed point -/

























/-! ### Strategy 4 on a predetermined query list -/

namespace RandomSearch





























end RandomSearch

end FullFormalization

open FullFormalization

set_option linter.unusedSectionVars false
variable {E : Type*}

open FullFormalization in

theorem solution (o : Oracle E) (a : E) (xs : List E) (b : E)
    (h : xs.foldl (bestStep o) (some a) = some b) : b ∈ a :: xs := by
  induction xs generalizing a with
  | nil =>
      rw [List.foldl_nil, Option.some.injEq] at h
      rw [h]
      simp
  | cons x xs ih =>
      rw [List.foldl_cons] at h
      simp only [bestStep] at h
      have hmem := ih (if o.value x < o.value a then x else a) h
      rcases List.mem_cons.mp hmem with hb | hb
      · by_cases hlt : o.value x < o.value a
        · rw [if_pos hlt] at hb; rw [hb]; simp
        · rw [if_neg hlt] at hb; rw [hb]; simp
      · exact List.mem_cons_of_mem a (List.mem_cons_of_mem x hb)
