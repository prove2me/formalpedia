-- Prove2me | solution 1 for ClauseBound.Grid.sum_le_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:34:19.341183+00:00
-- url     : https://prove2.me/submissions/5579d168-6c2a-425d-adad-98448426937f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ #s * c :=
  (Finset.sum_le_sum h).trans (Finset.sum_const_nat fun _ _ => rfl).le
end ClauseBound.Grid
