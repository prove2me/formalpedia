-- Prove2me | solution 1 for Eight.ViaGrouping.stLevelKeepsP_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:40.779056+00:00
-- url     : https://prove2.me/submissions/68472aa9-0bbd-435e-b747-64ead638f468

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_Level_Cert
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Theorems.Thm_Eight_ViaGrouping_levelProcs_keepsP
import Theorems.Thm_Eight_Level_Cert_div_polyT
import Theorems.Thm_Eight_Level_Cert_numPat8_polyT
import Theorems.Thm_Eight_Level_Cert_useRowP_polyT


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (h : Eight.StKeeps) : StLevelKeepsP := by
  intro g psiR psiC NA hpR hpC hN C _ _ _ lam R hl hR
  obtain ⟨h1⟩ := hN _ _ (levelProcs_keepsP h g false hpR C lam R hl hR)
  obtain ⟨h2⟩ := hN _ _ (levelProcs_keepsP h g true hpC C lam R hl hR)
  have h3 := IsPolyT.ite (M := NA.app (levelProcs g false psiR lam R)) (N := NA.app (levelProcs g true psiC lam R)) (Level.Cert.useRowP_polyT (C := C) h g hl)
  have h4 := IsPolyT.sumRange (M := Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R)))
    (Level.Cert.numPat8_polyT g hl)
  have h5 := IsPolyT.ofFun (Level.Cert.div_polyT (C := C) g hl)
  exact ⟨IsPolyT.bind⟩
end Eight.ViaGrouping
