-- Prove2me | solution 1 for Eidos.Tests.vulnerable_rule_is_not_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:37.895601+00:00
-- url     : https://prove2.me/submissions/3f615a14-695a-4167-83aa-8fc81e537387

import Definitions.Def_Eidos
import Definitions.Def_EidosTests
import Theorems.Thm_Eidos_Examples_Reserve_vulnerable_counterexample


set_option autoImplicit false
open Eidos Eidos.Tests
open Ergo Examples.Reserve
namespace Eidos.Tests
theorem _root_.solution :
    ¬ (∀ ctx, Accepts vulnerableScript ctx → WithdrawalBounded exampleReserve ctx) := by
  intro h
  exact vulnerable_counterexample.2 (h attackContext vulnerable_counterexample.1)
end Eidos.Tests
