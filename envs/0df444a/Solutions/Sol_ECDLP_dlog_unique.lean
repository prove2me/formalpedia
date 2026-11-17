-- Prove2me | solution 1 for ECDLP.dlog_unique
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:10:45.455204+00:00
-- url     : https://prove2.me/submissions/5879369d-ee21-433e-a785-70fba0e78aae

import Mathlib

namespace ECDLP

theorem dlog_unique {G : Type*} [AddCommGroup G] {P : G} {n : ℕ}
    (hP : addOrderOf P = n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : a • P = b • P) : a = b := by
  subst hP
  exact nsmul_injOn_Iio_addOrderOf ha hb h

end ECDLP

theorem solution {G : Type*} [AddCommGroup G] {P : G} {n : ℕ}
    (hP : addOrderOf P = n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : a • P = b • P) : a = b := ECDLP.dlog_unique hP ha hb h
