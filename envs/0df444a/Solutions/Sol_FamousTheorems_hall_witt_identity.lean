-- Prove2me | solution 1 for FamousTheorems.hall_witt_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:38:09.060985+00:00
-- url     : https://prove2.me/submissions/464febc0-e57a-4cd2-abf4-4b533045f17e

import Mathlib

open scoped commutatorElement

theorem solution {G : Type*} [Group G] (a b c : G) :
    ⁅⁅a, b⁆, b * c * b⁻¹⁆ * ⁅⁅b, c⁆, c * a * c⁻¹⁆ * ⁅⁅c, a⁆, a * b * a⁻¹⁆ = 1 :=
  commutatorElement_commutatorElement_conj_mul a b c
