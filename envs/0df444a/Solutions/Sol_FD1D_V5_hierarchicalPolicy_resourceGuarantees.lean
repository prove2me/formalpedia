-- Prove2me | solution 1 for FD1D.V5.hierarchicalPolicy_resourceGuarantees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:59.634875+00:00
-- url     : https://prove2.me/submissions/e959c51d-b780-42f5-9dc3-72f8891e2d30

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
import Theorems.Thm_FD1D_V5_hierarchicalMemoryCount_le_five_mul
import Theorems.Thm_FD1D_V5_hierarchicalOperationCount_cast_le_log
import Theorems.Thm_FD1D_V5_hierarchicalOperationCount_isBigO_log
import Theorems.Thm_FD1D_V5_hierarchicalMemoryCount_isBigO_linear

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution :
    HierarchicalResourceGuarantees where
  operationsExplicit := hierarchicalOperationCount_cast_le_log
  memoryExplicit := hierarchicalMemoryCount_le_five_mul
  operationsAsymptotic := hierarchicalOperationCount_isBigO_log
  memoryAsymptotic := hierarchicalMemoryCount_isBigO_linear
end FD1D.V5
