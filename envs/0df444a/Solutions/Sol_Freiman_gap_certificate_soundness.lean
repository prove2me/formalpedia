-- Prove2me | solution 1 for Freiman.gap_certificate_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:18.550861+00:00
-- url     : https://prove2.me/submissions/0f27356e-c501-4792-b764-0b5d38e06978

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_partition_coverage
import Theorems.Thm_Freiman_gap_leaf_soundness

open Freiman

theorem solution : GapCertificateSoundness := by
  intro lower upper mode tree a i hd hc hl hu hv hchecks hm
  obtain ⟨s,r,hr,hs⟩ := gap_partition_coverage tree a i hd hv hm
  exact gap_leaf_soundness lower upper mode s a i hd hc hl hu hs r (hchecks (s,r) hr)
