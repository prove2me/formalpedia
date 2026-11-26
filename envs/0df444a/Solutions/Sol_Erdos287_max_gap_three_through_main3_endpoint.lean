-- Prove2me | solution 1 for Erdos287.max_gap_three_through_main3_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:06:15.42308+00:00
-- url     : https://prove2.me/submissions/6d72d8c1-c15f-4bff-9b51-dad39a792e55

import Mathlib
import Theorems.Thm_Erdos287_max_gap_three_through_main2_endpoint
import Theorems.Thm_Erdos287_gap_three_in_compact_first_wide_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_1_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_2_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_3_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_4_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_5_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_6_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_7_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_8_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_9_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_10_band
import Theorems.Thm_Erdos287_gap_three_in_compact_wide_11_band

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435) : ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  by_cases hbase : f (k - 1) ≤ 858988211239796718174213
  · exact Erdos287.max_gap_three_through_main2_endpoint k hk f hf1 hmono hsum hbase
  by_cases h0 : f (k - 1) ≤ 740570313355511917542635417831997435
  · exact Erdos287.gap_three_in_compact_first_wide_band k hk f hf1 hmono hsum (by omega) h0
  by_cases h1 : f (k - 1) ≤ 638040061592254890692656715489809416283561656330
  · exact Erdos287.gap_three_in_compact_wide_1_band k hk f hf1 hmono hsum (by omega) h1
  by_cases h2 : f (k - 1) ≤ 541652714334911275455338317345215128734636854357567010242570
  · exact Erdos287.gap_three_in_compact_wide_2_band k hk f hf1 hmono hsum (by omega) h2
  by_cases h3 : f (k - 1) ≤ 459783374368222904827056593518393074552324179891101421807809742577336330
  · exact Erdos287.gap_three_in_compact_wide_3_band k hk f hf1 hmono hsum (by omega) h3
  by_cases h4 : f (k - 1) ≤ 387705887984591711416546378186759000448837202053331156305529786801988604734377820170
  · exact Erdos287.gap_three_in_compact_wide_4_band k hk f hf1 hmono hsum (by omega) h4
  by_cases h5 : f (k - 1) ≤ 321044521188307171763396601049205737020336364359631570294888556356534994101563402720486002524155
  · exact Erdos287.gap_three_in_compact_wide_5_band k hk f hf1 hmono hsum (by omega) h5
  by_cases h6 : f (k - 1) ≤ 263588884858131783375371140402679714449945424711319890847933073159865856950104334566089736438554049862696955
  · exact Erdos287.gap_three_in_compact_wide_6_band k hk f hf1 hmono hsum (by omega) h6
  by_cases h7 : f (k - 1) ≤ 214159363982694220762791838234441303966448576564395913178069362933275385011193945334184159829056850097682828246510469130
  · exact Erdos287.gap_three_in_compact_wide_7_band k hk f hf1 hmono hsum (by omega) h7
  by_cases h8 : f (k - 1) ≤ 171263047019454982187902002972189565750774750531772130904218567038142881202301234376428697124127793733990087232756415489182395269130
  · exact Erdos287.gap_three_in_compact_wide_8_band k hk f hf1 hmono hsum (by omega) h8
  by_cases h9 : f (k - 1) ≤ 136559784184233651339964983168638167802625998357313169802851241637946516165847788502240036591291824531654297049080916930261764820795589719490570
  · exact Erdos287.gap_three_in_compact_wide_9_band k hk f hf1 hmono hsum (by omega) h9
  by_cases h10 : f (k - 1) ≤ 103091558235810307556758383984131383502338270262018175758223050084115981815857437218079654870252928856883491762045970221421952527076000397762791792506306555
  · exact Erdos287.gap_three_in_compact_wide_10_band k hk f hf1 hmono hsum (by omega) h10
  exact Erdos287.gap_three_in_compact_wide_11_band k hk f hf1 hmono hsum (by omega) hbound

