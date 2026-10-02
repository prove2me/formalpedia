-- Prove2me | solution 1 for ChebotarevDensity.cyclePattern_conj
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:28:10.861984+00:00
-- url     : https://prove2.me/submissions/f0bbff9f-0b73-45d0-a46d-34aae229da88

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField
open ChebotarevDensity

private lemma parts_eq_of_cycleType_eq {α : Type*} [Fintype α] [DecidableEq α]
    (a b : Equiv.Perm α) (h : a.cycleType = b.cycleType) :
    a.partition.parts = b.partition.parts := by
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition, h]
  have h1 := Equiv.Perm.sum_cycleType a
  have h2 := Equiv.Perm.sum_cycleType b
  rw [h] at h1
  have : a.support.card = b.support.card := by omega
  rw [this]

theorem solution (f : ℤ[X]) (g x : GalGroup f) :
    cyclePattern f (x * g * x⁻¹) = cyclePattern f g := by
  unfold cyclePattern
  refine parts_eq_of_cycleType_eq _ _ ?_
  rw [map_mul, map_mul, map_inv]
  exact Equiv.Perm.cycleType_conj

