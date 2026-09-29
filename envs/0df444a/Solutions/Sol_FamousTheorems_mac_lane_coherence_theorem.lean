-- Prove2me | solution 1 for FamousTheorems.mac_lane_coherence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:51:44.365316+00:00
-- url     : https://prove2.me/submissions/facefa98-9e02-480f-acf4-75b80b57b8c7

import Mathlib

theorem solution (C : Type*) : Quiver.IsThin (CategoryTheory.FreeMonoidalCategory C) :=
  CategoryTheory.FreeMonoidalCategory.subsingleton_hom
