-- Prove2me | solution 1 for FamousTheorems.grothendieck_abelian_enough_injectives_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:05:40.425176+00:00
-- url     : https://prove2.me/submissions/ad290095-7e92-4638-853b-7d5944226733

import Mathlib

universe u v w

theorem solution (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{w} C] : CategoryTheory.EnoughInjectives C :=
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives
