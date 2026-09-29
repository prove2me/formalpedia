-- Prove2me | solution 1 for FamousTheorems.gabriel_popescu_full_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:15:27.305177+00:00
-- url     : https://prove2.me/submissions/83f4e9fe-fc48-4cd1-a1fc-5211bb10ab0c

import Mathlib

universe u v

theorem solution {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{v} C] (G : C) (hG : CategoryTheory.IsSeparator G) :
    (CategoryTheory.preadditiveCoyonedaObj G).Full :=
  CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.full G hG
