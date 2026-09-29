-- Prove2me | solution 1 for Gelbart.hecke_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:32:07.757519+00:00
-- url     : https://prove2.me/submissions/09d0ac7a-144c-4a9e-a3e1-83340257ef7e

import Definitions.Def_Gelbart_hecke_conditions
import Theorems.Thm_Gelbart_hecke_nice_of_automorphic
import Theorems.Thm_Gelbart_hecke_automorphic_of_nice

namespace Gelbart

theorem _root_.solution
    (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ)
    (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) (hC : C = 1 ∨ C = -1)
    (hgrowth : HeckeCoeffGrowth a c) :
    HeckeNice a h k C (c + 1) ↔ HeckeAutomorphic a h k C :=
  ⟨hecke_automorphic_of_nice a c h k C hc hh hk hC hgrowth,
    hecke_nice_of_automorphic a c h k C hc hh hk hC hgrowth⟩

end Gelbart
