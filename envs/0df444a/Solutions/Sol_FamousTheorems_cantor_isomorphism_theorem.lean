-- Prove2me | solution 1 for FamousTheorems.cantor_isomorphism_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:25:52.43357+00:00
-- url     : https://prove2.me/submissions/3ba09224-52e8-4b52-a775-6ab0fba64f51

import Mathlib

theorem solution (α β : Type*) [LinearOrder α] [LinearOrder β] [Countable α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) :=
  Order.iso_of_countable_dense α β
