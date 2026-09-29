-- Prove2me | solution 1 for Freiman.lower_bridge_endpoint_application
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:38:19.801486+00:00
-- url     : https://prove2.me/submissions/1a604ef6-1061-4d49-81b0-093c9a85dd36

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section
open Freiman
namespace OtherBridgeEndpoint
private theorem normalize_parity (p : LowerPair) (hp : p.1.length%2=p.2.length%2) :
    (lowerNormalize p).1.length%2=(lowerNormalize p).2.length%2 := by
  unfold lowerNormalize
  split
  · exact hp
  · exact hp.symm
private theorem bridge_parity (c : LowerBridgeCase) (n k : ℕ) :
    (lowerBridgePair c n k).1.length%2=(lowerBridgePair c n k).2.length%2 := by
  unfold lowerBridgePair
  apply normalize_parity
  cases c <;> simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily,
    lowerFamilyPair, List.length_append] <;> omega
private theorem ends_append (p t s : List ℕ+) (h : s.length ≤ t.length) :
    s.IsSuffix (p++t) ↔ s.IsSuffix t :=
  ⟨fun hh => List.suffix_of_suffix_length_le hh (List.suffix_append p t) h,
    fun hh => List.suffix_append_of_suffix hh⟩
private theorem endpoint_aZero (n k : ℕ) (h : lowerBridgeFacts .aZero n k) :
    lowerBridgeEndpointFacts .aZero n k := by
  have hp := bridge_parity LowerBridgeCase.aZero n k
  have h0 : lowerWidth ((lowerBridgePair .aZero n k).2++[1]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1]) := h ((lowerBridgeRecords .aZero)[0]'(by decide)) (List.getElem_mem _)
  have h0le := (h0).le
  have h0nle := not_le.mpr h0
  have h3 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2]) := h ((lowerBridgeRecords .aZero)[3]'(by decide)) (List.getElem_mem _)
  have h3le := (h3).le
  have h3nle := not_le.mpr h3
  have h4 : lowerWidth (((lowerBridgePair .aZero n k).1++[1,2])++[1,3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2])++[1,3]) := h ((lowerBridgeRecords .aZero)[4]'(by decide)) (List.getElem_mem _)
  have h5 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[5]'(by decide)) (List.getElem_mem _)
  have h5le := (h5).le
  have h5nle := not_le.mpr h5
  have h6 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[6]'(by decide)) (List.getElem_mem _)
  have h6le := (h6).le
  have h6nle := not_le.mpr h6
  have h7 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[7]'(by decide)) (List.getElem_mem _)
  have h7le := (h7).le
  have h7nle := not_le.mpr h7
  have h8 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aZero)[8]'(by decide)) (List.getElem_mem _)
  have h8le := (h8).le
  have h8nle := not_le.mpr h8
  have h10 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[10]'(by decide)) (List.getElem_mem _)
  have h10le := (h10).le
  have h10nle := not_le.mpr h10
  have h11 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[11]'(by decide)) (List.getElem_mem _)
  have h11le := (h11).le
  have h11nle := not_le.mpr h11
  have h12 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aZero)[12]'(by decide)) (List.getElem_mem _)
  have h12le := (h12).le
  have h12nle := not_le.mpr h12
  have h14 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[14]'(by decide)) (List.getElem_mem _)
  have h14le := (h14).le
  have h14nle := not_le.mpr h14
  have h15 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[15]'(by decide)) (List.getElem_mem _)
  have h15le := (h15).le
  have h15nle := not_le.mpr h15
  have h16 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[16]'(by decide)) (List.getElem_mem _)
  have h16le := (h16).le
  have h16nle := not_le.mpr h16
  have h17 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[17]'(by decide)) (List.getElem_mem _)
  have h17le := (h17).le
  have h17nle := not_le.mpr h17
  have h19 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[19]'(by decide)) (List.getElem_mem _)
  have h19le := (h19).le
  have h19nle := not_le.mpr h19
  have h20 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[20]'(by decide)) (List.getElem_mem _)
  have h20le := (h20).le
  have h20nle := not_le.mpr h20
  have h21 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[21]'(by decide)) (List.getElem_mem _)
  have h21le := (h21).le
  have h21nle := not_le.mpr h21
  have h23 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2]) := h ((lowerBridgeRecords .aZero)[23]'(by decide)) (List.getElem_mem _)
  have h23le := (h23).le
  have h23nle := not_le.mpr h23
  have h24 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[24]'(by decide)) (List.getElem_mem _)
  have h24le := (h24).le
  have h24nle := not_le.mpr h24
  have h25 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[25]'(by decide)) (List.getElem_mem _)
  have h25le := (h25).le
  have h25nle := not_le.mpr h25
  have h26 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2,1]) := h ((lowerBridgeRecords .aZero)[26]'(by decide)) (List.getElem_mem _)
  have h26le := (h26).le
  have h26nle := not_le.mpr h26
  have h27 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,2])++[3]) < lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2,1])++[3]) := h ((lowerBridgeRecords .aZero)[27]'(by decide)) (List.getElem_mem _)
  have h27le := (h27).le
  have h27nle := not_le.mpr h27
  have h29 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[29]'(by decide)) (List.getElem_mem _)
  have h29le := (h29).le
  have h29nle := not_le.mpr h29
  have h30 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[30]'(by decide)) (List.getElem_mem _)
  have h30le := (h30).le
  have h30nle := not_le.mpr h30
  have h31 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2,1]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,1]) := h ((lowerBridgeRecords .aZero)[31]'(by decide)) (List.getElem_mem _)
  have h31le := (h31).le
  have h31nle := not_le.mpr h31
  have h32 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2,1])++[3]) < lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2,1])++[3]) := h ((lowerBridgeRecords .aZero)[32]'(by decide)) (List.getElem_mem _)
  have h32le := (h32).le
  have h32nle := not_le.mpr h32
  have h34 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[34]'(by decide)) (List.getElem_mem _)
  have h34le := (h34).le
  have h34nle := not_le.mpr h34
  have h35 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[35]'(by decide)) (List.getElem_mem _)
  have h35le := (h35).le
  have h35nle := not_le.mpr h35
  have h36 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[36]'(by decide)) (List.getElem_mem _)
  have h36le := (h36).le
  have h36nle := not_le.mpr h36
  have h37 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[37]'(by decide)) (List.getElem_mem _)
  have h37le := (h37).le
  have h37nle := not_le.mpr h37
  have h39 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[39]'(by decide)) (List.getElem_mem _)
  have h39le := (h39).le
  have h39nle := not_le.mpr h39
  have h40 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[40]'(by decide)) (List.getElem_mem _)
  have h40le := (h40).le
  have h40nle := not_le.mpr h40
  have h41 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[41]'(by decide)) (List.getElem_mem _)
  have h41le := (h41).le
  have h41nle := not_le.mpr h41
  have h43 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[43]'(by decide)) (List.getElem_mem _)
  have h43le := (h43).le
  have h43nle := not_le.mpr h43
  have h44 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[44]'(by decide)) (List.getElem_mem _)
  have h44le := (h44).le
  have h44nle := not_le.mpr h44
  have h45 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1]) := h ((lowerBridgeRecords .aZero)[45]'(by decide)) (List.getElem_mem _)
  have h45le := (h45).le
  have h45nle := not_le.mpr h45
  have h46 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[46]'(by decide)) (List.getElem_mem _)
  have h46le := (h46).le
  have h46nle := not_le.mpr h46
  have h48 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[48]'(by decide)) (List.getElem_mem _)
  have h48le := (h48).le
  have h48nle := not_le.mpr h48
  have h49 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,1]) := h ((lowerBridgeRecords .aZero)[49]'(by decide)) (List.getElem_mem _)
  have h49le := (h49).le
  have h49nle := not_le.mpr h49
  have h50 : lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[50]'(by decide)) (List.getElem_mem _)
  have h50le := (h50).le
  have h50nle := not_le.mpr h50
  have h52 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[52]'(by decide)) (List.getElem_mem _)
  have h52le := (h52).le
  have h52nle := not_le.mpr h52
  have h54 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[54]'(by decide)) (List.getElem_mem _)
  have h54le := (h54).le
  have h54nle := not_le.mpr h54
  have h55 : lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,3,3])++[3]) := h ((lowerBridgeRecords .aZero)[55]'(by decide)) (List.getElem_mem _)
  have h56 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[56]'(by decide)) (List.getElem_mem _)
  have h56le := (h56).le
  have h56nle := not_le.mpr h56
  have h58 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[58]'(by decide)) (List.getElem_mem _)
  have h58le := (h58).le
  have h58nle := not_le.mpr h58
  have h59 : lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3,3])++[3]) := h ((lowerBridgeRecords .aZero)[59]'(by decide)) (List.getElem_mem _)
  have h60 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2]) := h ((lowerBridgeRecords .aZero)[60]'(by decide)) (List.getElem_mem _)
  have h60le := (h60).le
  have h60nle := not_le.mpr h60
  have h61 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2])++[1,3]) < lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2])++[1,3]) := h ((lowerBridgeRecords .aZero)[61]'(by decide)) (List.getElem_mem _)
  have h61le := (h61).le
  have h61nle := not_le.mpr h61
  have h63 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2]) := h ((lowerBridgeRecords .aZero)[63]'(by decide)) (List.getElem_mem _)
  have h63le := (h63).le
  have h63nle := not_le.mpr h63
  have h64 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,2,1,3,1,3,2])++[3]) < lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,1,3,1,2,2])++[3]) := h ((lowerBridgeRecords .aZero)[64]'(by decide)) (List.getElem_mem _)
  have h64le := (h64).le
  have h64nle := not_le.mpr h64
  have h65 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[65]'(by decide)) (List.getElem_mem _)
  have h65le := (h65).le
  have h65nle := not_le.mpr h65
  have h66 : lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3])++[3]) := h ((lowerBridgeRecords .aZero)[66]'(by decide)) (List.getElem_mem _)
  have h68 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[68]'(by decide)) (List.getElem_mem _)
  have h68le := (h68).le
  have h68nle := not_le.mpr h68
  have h69 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[69]'(by decide)) (List.getElem_mem _)
  have h69le := (h69).le
  have h69nle := not_le.mpr h69
  have h70 : lowerWidth (((lowerBridgePair .aZero n k).1++[1,2,1,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n k).2++[1,2,1,3])++[3]) := h ((lowerBridgeRecords .aZero)[70]'(by decide)) (List.getElem_mem _)
  have h72 : lowerWidth ((lowerBridgePair .aZero n k).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aZero n k).1++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[72]'(by decide)) (List.getElem_mem _)
  have h72le := (h72).le
  have h72nle := not_le.mpr h72
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h0le h0nle h3 h3le h3nle h4 h5 h5le h5nle h6 h6le h6nle h7 h7le h7nle h8 h8le h8nle h10 h10le h10nle h11 h11le h11nle h12 h12le h12nle h14 h14le h14nle h15 h15le h15nle h16 h16le h16nle h17 h17le h17nle h19 h19le h19nle h20 h20le h20nle h21 h21le h21nle h23 h23le h23nle h24 h24le h24nle h25 h25le h25nle h26 h26le h26nle h27 h27le h27nle h29 h29le h29nle h30 h30le h30nle h31 h31le h31nle h32 h32le h32nle h34 h34le h34nle h35 h35le h35nle h36 h36le h36nle h37 h37le h37nle h39 h39le h39nle h40 h40le h40nle h41 h41le h41nle h43 h43le h43nle h44 h44le h44nle h45 h45le h45nle h46 h46le h46nle h48 h48le h48nle h49 h49le h49nle h50 h50le h50nle h52 h52le h52nle h54 h54le h54nle h55 h56 h56le h56nle h58 h58le h58nle h59 h60 h60le h60nle h61 h61le h61nle h63 h63le h63nle h64 h64le h64nle h65 h65le h65nle h66 h68 h68le h68nle h69 h69le h69nle h70 h72 h72le h72nle
  intro e he
  simp only [lowerBridgeEndpoints, lowerBridgeEndpoints_aZero, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [lowerBridgeEndpointFact, lowerBridgeAppend]
    rcases Nat.mod_two_eq_zero_or_one (lowerBridgePair .aZero n k).1.length with hp0 | hp0
    all_goals
      have hp2 : (lowerBridgePair .aZero n k).2.length % 2 = (lowerBridgePair .aZero n k).1.length % 2 := hp.symm
      simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerNormalize, lowerEnds, ends_append, List.suffix_cons_iff, List.length_append,
        hp2, hp0, Nat.add_mod, List.append_assoc, h0, h0le, h0nle, h3, h3le, h3nle, h4, h5, h5le, h5nle, h6, h6le, h6nle, h7, h7le, h7nle, h8, h8le, h8nle, h10, h10le, h10nle, h11, h11le, h11nle, h12, h12le, h12nle, h14, h14le, h14nle, h15, h15le, h15nle, h16, h16le, h16nle, h17, h17le, h17nle, h19, h19le, h19nle, h20, h20le, h20nle, h21, h21le, h21nle, h23, h23le, h23nle, h24, h24le, h24nle, h25, h25le, h25nle, h26, h26le, h26nle, h27, h27le, h27nle, h29, h29le, h29nle, h30, h30le, h30nle, h31, h31le, h31nle, h32, h32le, h32nle, h34, h34le, h34nle, h35, h35le, h35nle, h36, h36le, h36nle, h37, h37le, h37nle, h39, h39le, h39nle, h40, h40le, h40nle, h41, h41le, h41nle, h43, h43le, h43nle, h44, h44le, h44nle, h45, h45le, h45nle, h46, h46le, h46nle, h48, h48le, h48nle, h49, h49le, h49nle, h50, h50le, h50nle, h52, h52le, h52nle, h54, h54le, h54nle, h55, h56, h56le, h56nle, h58, h58le, h58nle, h59, h60, h60le, h60nle, h61, h61le, h61nle, h63, h63le, h63nle, h64, h64le, h64nle, h65, h65le, h65nle, h66, h68, h68le, h68nle, h69, h69le, h69nle, h70, h72, h72le, h72nle]

private theorem endpoint_aPos (n k : ℕ) (h : lowerBridgeFacts .aPos n k) :
    lowerBridgeEndpointFacts .aPos n k := by
  have hp := bridge_parity LowerBridgeCase.aPos n k
  have h0 : lowerWidth ((lowerBridgePair .aPos n k).2++[1]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1]) := h ((lowerBridgeRecords .aPos)[0]'(by decide)) (List.getElem_mem _)
  have h0le := (h0).le
  have h0nle := not_le.mpr h0
  have h3 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2]) := h ((lowerBridgeRecords .aPos)[3]'(by decide)) (List.getElem_mem _)
  have h3le := (h3).le
  have h3nle := not_le.mpr h3
  have h4 : lowerWidth (((lowerBridgePair .aPos n k).1++[1,2])++[1,3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2])++[1,3]) := h ((lowerBridgeRecords .aPos)[4]'(by decide)) (List.getElem_mem _)
  have h5 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[5]'(by decide)) (List.getElem_mem _)
  have h5le := (h5).le
  have h5nle := not_le.mpr h5
  have h6 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[6]'(by decide)) (List.getElem_mem _)
  have h6le := (h6).le
  have h6nle := not_le.mpr h6
  have h7 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[7]'(by decide)) (List.getElem_mem _)
  have h7le := (h7).le
  have h7nle := not_le.mpr h7
  have h8 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aPos)[8]'(by decide)) (List.getElem_mem _)
  have h8le := (h8).le
  have h8nle := not_le.mpr h8
  have h10 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[10]'(by decide)) (List.getElem_mem _)
  have h10le := (h10).le
  have h10nle := not_le.mpr h10
  have h11 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[11]'(by decide)) (List.getElem_mem _)
  have h11le := (h11).le
  have h11nle := not_le.mpr h11
  have h12 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aPos)[12]'(by decide)) (List.getElem_mem _)
  have h12le := (h12).le
  have h12nle := not_le.mpr h12
  have h14 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1]) := h ((lowerBridgeRecords .aPos)[14]'(by decide)) (List.getElem_mem _)
  have h14le := (h14).le
  have h14nle := not_le.mpr h14
  have h15 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,1]) := h ((lowerBridgeRecords .aPos)[15]'(by decide)) (List.getElem_mem _)
  have h15le := (h15).le
  have h15nle := not_le.mpr h15
  have h16 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,1,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aPos)[16]'(by decide)) (List.getElem_mem _)
  have h16le := (h16).le
  have h16nle := not_le.mpr h16
  have h17 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,1,1])++[3]) < lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2])++[3]) := h ((lowerBridgeRecords .aPos)[17]'(by decide)) (List.getElem_mem _)
  have h17le := (h17).le
  have h17nle := not_le.mpr h17
  have h18 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aPos)[18]'(by decide)) (List.getElem_mem _)
  have h18le := (h18).le
  have h18nle := not_le.mpr h18
  have h19 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2,1]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,2]) := h ((lowerBridgeRecords .aPos)[19]'(by decide)) (List.getElem_mem _)
  have h19le := (h19).le
  have h19nle := not_le.mpr h19
  have h20 : lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,2])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2,1])++[3]) := h ((lowerBridgeRecords .aPos)[20]'(by decide)) (List.getElem_mem _)
  have h22 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aPos)[22]'(by decide)) (List.getElem_mem _)
  have h22le := (h22).le
  have h22nle := not_le.mpr h22
  have h23 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1,1]) := h ((lowerBridgeRecords .aPos)[23]'(by decide)) (List.getElem_mem _)
  have h23le := (h23).le
  have h23nle := not_le.mpr h23
  have h25 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[25]'(by decide)) (List.getElem_mem _)
  have h25le := (h25).le
  have h25nle := not_le.mpr h25
  have h26 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[26]'(by decide)) (List.getElem_mem _)
  have h26le := (h26).le
  have h26nle := not_le.mpr h26
  have h27 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aPos)[27]'(by decide)) (List.getElem_mem _)
  have h27le := (h27).le
  have h27nle := not_le.mpr h27
  have h28 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[28]'(by decide)) (List.getElem_mem _)
  have h28le := (h28).le
  have h28nle := not_le.mpr h28
  have h30 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[30]'(by decide)) (List.getElem_mem _)
  have h30le := (h30).le
  have h30nle := not_le.mpr h30
  have h31 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aPos)[31]'(by decide)) (List.getElem_mem _)
  have h31le := (h31).le
  have h31nle := not_le.mpr h31
  have h32 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[32]'(by decide)) (List.getElem_mem _)
  have h32le := (h32).le
  have h32nle := not_le.mpr h32
  have h34 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[34]'(by decide)) (List.getElem_mem _)
  have h34le := (h34).le
  have h34nle := not_le.mpr h34
  have h35 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[35]'(by decide)) (List.getElem_mem _)
  have h35le := (h35).le
  have h35nle := not_le.mpr h35
  have h36 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1]) := h ((lowerBridgeRecords .aPos)[36]'(by decide)) (List.getElem_mem _)
  have h36le := (h36).le
  have h36nle := not_le.mpr h36
  have h37 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[37]'(by decide)) (List.getElem_mem _)
  have h37le := (h37).le
  have h37nle := not_le.mpr h37
  have h39 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[39]'(by decide)) (List.getElem_mem _)
  have h39le := (h39).le
  have h39nle := not_le.mpr h39
  have h40 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,1]) := h ((lowerBridgeRecords .aPos)[40]'(by decide)) (List.getElem_mem _)
  have h40le := (h40).le
  have h40nle := not_le.mpr h40
  have h41 : lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[41]'(by decide)) (List.getElem_mem _)
  have h41le := (h41).le
  have h41nle := not_le.mpr h41
  have h43 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[43]'(by decide)) (List.getElem_mem _)
  have h43le := (h43).le
  have h43nle := not_le.mpr h43
  have h45 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[45]'(by decide)) (List.getElem_mem _)
  have h45le := (h45).le
  have h45nle := not_le.mpr h45
  have h46 : lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,3,3])++[3]) := h ((lowerBridgeRecords .aPos)[46]'(by decide)) (List.getElem_mem _)
  have h47 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1]) := h ((lowerBridgeRecords .aPos)[47]'(by decide)) (List.getElem_mem _)
  have h47le := (h47).le
  have h47nle := not_le.mpr h47
  have h48 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2])++[1,3]) < lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1])++[1,3]) := h ((lowerBridgeRecords .aPos)[48]'(by decide)) (List.getElem_mem _)
  have h48le := (h48).le
  have h48nle := not_le.mpr h48
  have h50 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1]) := h ((lowerBridgeRecords .aPos)[50]'(by decide)) (List.getElem_mem _)
  have h50le := (h50).le
  have h50nle := not_le.mpr h50
  have h51 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,2,1,3,1,3,2])++[3]) < lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3,1,3,1,2,1])++[3]) := h ((lowerBridgeRecords .aPos)[51]'(by decide)) (List.getElem_mem _)
  have h51le := (h51).le
  have h51nle := not_le.mpr h51
  have h52 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[52]'(by decide)) (List.getElem_mem _)
  have h52le := (h52).le
  have h52nle := not_le.mpr h52
  have h53 : lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3])++[3]) := h ((lowerBridgeRecords .aPos)[53]'(by decide)) (List.getElem_mem _)
  have h55 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[55]'(by decide)) (List.getElem_mem _)
  have h55le := (h55).le
  have h55nle := not_le.mpr h55
  have h56 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[56]'(by decide)) (List.getElem_mem _)
  have h56le := (h56).le
  have h56nle := not_le.mpr h56
  have h57 : lowerWidth (((lowerBridgePair .aPos n k).1++[1,2,1,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n k).2++[1,2,1,3])++[3]) := h ((lowerBridgeRecords .aPos)[57]'(by decide)) (List.getElem_mem _)
  have h59 : lowerWidth ((lowerBridgePair .aPos n k).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aPos n k).1++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[59]'(by decide)) (List.getElem_mem _)
  have h59le := (h59).le
  have h59nle := not_le.mpr h59
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h0le h0nle h3 h3le h3nle h4 h5 h5le h5nle h6 h6le h6nle h7 h7le h7nle h8 h8le h8nle h10 h10le h10nle h11 h11le h11nle h12 h12le h12nle h14 h14le h14nle h15 h15le h15nle h16 h16le h16nle h17 h17le h17nle h18 h18le h18nle h19 h19le h19nle h20 h22 h22le h22nle h23 h23le h23nle h25 h25le h25nle h26 h26le h26nle h27 h27le h27nle h28 h28le h28nle h30 h30le h30nle h31 h31le h31nle h32 h32le h32nle h34 h34le h34nle h35 h35le h35nle h36 h36le h36nle h37 h37le h37nle h39 h39le h39nle h40 h40le h40nle h41 h41le h41nle h43 h43le h43nle h45 h45le h45nle h46 h47 h47le h47nle h48 h48le h48nle h50 h50le h50nle h51 h51le h51nle h52 h52le h52nle h53 h55 h55le h55nle h56 h56le h56nle h57 h59 h59le h59nle
  intro e he
  simp only [lowerBridgeEndpoints, lowerBridgeEndpoints_aPos, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [lowerBridgeEndpointFact, lowerBridgeAppend]
    rcases Nat.mod_two_eq_zero_or_one (lowerBridgePair .aPos n k).1.length with hp0 | hp0
    all_goals
      have hp2 : (lowerBridgePair .aPos n k).2.length % 2 = (lowerBridgePair .aPos n k).1.length % 2 := hp.symm
      simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerNormalize, lowerEnds, ends_append, List.suffix_cons_iff, List.length_append,
        hp2, hp0, Nat.add_mod, List.append_assoc, h0, h0le, h0nle, h3, h3le, h3nle, h4, h5, h5le, h5nle, h6, h6le, h6nle, h7, h7le, h7nle, h8, h8le, h8nle, h10, h10le, h10nle, h11, h11le, h11nle, h12, h12le, h12nle, h14, h14le, h14nle, h15, h15le, h15nle, h16, h16le, h16nle, h17, h17le, h17nle, h18, h18le, h18nle, h19, h19le, h19nle, h20, h22, h22le, h22nle, h23, h23le, h23nle, h25, h25le, h25nle, h26, h26le, h26nle, h27, h27le, h27nle, h28, h28le, h28nle, h30, h30le, h30nle, h31, h31le, h31nle, h32, h32le, h32nle, h34, h34le, h34nle, h35, h35le, h35nle, h36, h36le, h36nle, h37, h37le, h37nle, h39, h39le, h39nle, h40, h40le, h40nle, h41, h41le, h41nle, h43, h43le, h43nle, h45, h45le, h45nle, h46, h47, h47le, h47nle, h48, h48le, h48nle, h50, h50le, h50nle, h51, h51le, h51nle, h52, h52le, h52nle, h53, h55, h55le, h55nle, h56, h56le, h56nle, h57, h59, h59le, h59nle]

private theorem endpoint_bZero (n k : ℕ) (h : lowerBridgeFacts .bZero n k) :
    lowerBridgeEndpointFacts .bZero n k := by
  have hp := bridge_parity LowerBridgeCase.bZero n k
  have h0 : lowerWidth ((lowerBridgePair .bZero n k).2++[1]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1]) := h ((lowerBridgeRecords .bZero)[0]'(by decide)) (List.getElem_mem _)
  have h0le := (h0).le
  have h0nle := not_le.mpr h0
  have h3 : lowerWidth ((lowerBridgePair .bZero n k).2++[1,2]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1,2]) := h ((lowerBridgeRecords .bZero)[3]'(by decide)) (List.getElem_mem _)
  have h3le := (h3).le
  have h3nle := not_le.mpr h3
  have h4 : lowerWidth (((lowerBridgePair .bZero n k).1++[1,2])++[1,3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .bZero n k).2++[1,2])++[1,3]) := h ((lowerBridgeRecords .bZero)[4]'(by decide)) (List.getElem_mem _)
  have h5 : lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) < lowerWidth ((lowerBridgePair .bZero n k).2++[1,2]) := h ((lowerBridgeRecords .bZero)[5]'(by decide)) (List.getElem_mem _)
  have h5le := (h5).le
  have h5nle := not_le.mpr h5
  have h6 : lowerWidth ((lowerBridgePair .bZero n k).2++[1,2,1]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) := h ((lowerBridgeRecords .bZero)[6]'(by decide)) (List.getElem_mem _)
  have h6le := (h6).le
  have h6nle := not_le.mpr h6
  have h7 : lowerWidth ((lowerBridgePair .bZero n k).1++[1,3,1]) < lowerWidth ((lowerBridgePair .bZero n k).2++[1,2,1]) := h ((lowerBridgeRecords .bZero)[7]'(by decide)) (List.getElem_mem _)
  have h7le := (h7).le
  have h7nle := not_le.mpr h7
  have h8 : lowerWidth ((lowerBridgePair .bZero n k).2++[1,2,2]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) := h ((lowerBridgeRecords .bZero)[8]'(by decide)) (List.getElem_mem _)
  have h8le := (h8).le
  have h8nle := not_le.mpr h8
  have h10 : lowerWidth ((lowerBridgePair .bZero n k).2++[1,2,2]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) := h ((lowerBridgeRecords .bZero)[10]'(by decide)) (List.getElem_mem _)
  have h10le := (h10).le
  have h10nle := not_le.mpr h10
  have h11 : lowerWidth ((lowerBridgePair .bZero n k).2++[1,2,2]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1,3,1]) := h ((lowerBridgeRecords .bZero)[11]'(by decide)) (List.getElem_mem _)
  have h11le := (h11).le
  have h11nle := not_le.mpr h11
  have h12 : lowerWidth ((lowerBridgePair .bZero n k).2++[1,2,1]) < lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) := h ((lowerBridgeRecords .bZero)[12]'(by decide)) (List.getElem_mem _)
  have h12le := (h12).le
  have h12nle := not_le.mpr h12
  have h14 : lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) < lowerWidth ((lowerBridgePair .bZero n k).2++[1,2]) := h ((lowerBridgeRecords .bZero)[14]'(by decide)) (List.getElem_mem _)
  have h14le := (h14).le
  have h14nle := not_le.mpr h14
  have h15 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .bZero n k).1++[1,3])++[3]) < lowerWidth (((lowerBridgePair .bZero n k).2++[1,2])++[3]) := h ((lowerBridgeRecords .bZero)[15]'(by decide)) (List.getElem_mem _)
  have h15le := (h15).le
  have h15nle := not_le.mpr h15
  have h17 : lowerWidth ((lowerBridgePair .bZero n k).1++[1,3]) < lowerWidth ((lowerBridgePair .bZero n k).2++[1,2]) := h ((lowerBridgeRecords .bZero)[17]'(by decide)) (List.getElem_mem _)
  have h17le := (h17).le
  have h17nle := not_le.mpr h17
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h0le h0nle h3 h3le h3nle h4 h5 h5le h5nle h6 h6le h6nle h7 h7le h7nle h8 h8le h8nle h10 h10le h10nle h11 h11le h11nle h12 h12le h12nle h14 h14le h14nle h15 h15le h15nle h17 h17le h17nle
  intro e he
  simp only [lowerBridgeEndpoints, lowerBridgeEndpoints_bZero, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [lowerBridgeEndpointFact, lowerBridgeAppend]
    rcases Nat.mod_two_eq_zero_or_one (lowerBridgePair .bZero n k).1.length with hp0 | hp0
    all_goals
      have hp2 : (lowerBridgePair .bZero n k).2.length % 2 = (lowerBridgePair .bZero n k).1.length % 2 := hp.symm
      simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerNormalize, lowerEnds, ends_append, List.suffix_cons_iff, List.length_append,
        hp2, hp0, Nat.add_mod, List.append_assoc, h0, h0le, h0nle, h3, h3le, h3nle, h4, h5, h5le, h5nle, h6, h6le, h6nle, h7, h7le, h7nle, h8, h8le, h8nle, h10, h10le, h10nle, h11, h11le, h11nle, h12, h12le, h12nle, h14, h14le, h14nle, h15, h15le, h15nle, h17, h17le, h17nle]

private theorem endpoint_bPos (n k : ℕ) (h : lowerBridgeFacts .bPos n k) :
    lowerBridgeEndpointFacts .bPos n k := by
  have hp := bridge_parity LowerBridgeCase.bPos n k
  have h0 : lowerWidth ((lowerBridgePair .bPos n k).2++[1]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1]) := h ((lowerBridgeRecords .bPos)[0]'(by decide)) (List.getElem_mem _)
  have h0le := (h0).le
  have h0nle := not_le.mpr h0
  have h3 : lowerWidth ((lowerBridgePair .bPos n k).2++[1,2]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1,2]) := h ((lowerBridgeRecords .bPos)[3]'(by decide)) (List.getElem_mem _)
  have h3le := (h3).le
  have h3nle := not_le.mpr h3
  have h4 : lowerWidth (((lowerBridgePair .bPos n k).1++[1,2])++[1,3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .bPos n k).2++[1,2])++[1,3]) := h ((lowerBridgeRecords .bPos)[4]'(by decide)) (List.getElem_mem _)
  have h5 : lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) < lowerWidth ((lowerBridgePair .bPos n k).2++[1,2]) := h ((lowerBridgeRecords .bPos)[5]'(by decide)) (List.getElem_mem _)
  have h5le := (h5).le
  have h5nle := not_le.mpr h5
  have h6 : lowerWidth ((lowerBridgePair .bPos n k).2++[1,2,1]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) := h ((lowerBridgeRecords .bPos)[6]'(by decide)) (List.getElem_mem _)
  have h6le := (h6).le
  have h6nle := not_le.mpr h6
  have h7 : lowerWidth ((lowerBridgePair .bPos n k).1++[1,3,1]) < lowerWidth ((lowerBridgePair .bPos n k).2++[1,2,1]) := h ((lowerBridgeRecords .bPos)[7]'(by decide)) (List.getElem_mem _)
  have h7le := (h7).le
  have h7nle := not_le.mpr h7
  have h8 : lowerWidth ((lowerBridgePair .bPos n k).2++[1,2,2]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) := h ((lowerBridgeRecords .bPos)[8]'(by decide)) (List.getElem_mem _)
  have h8le := (h8).le
  have h8nle := not_le.mpr h8
  have h10 : lowerWidth ((lowerBridgePair .bPos n k).2++[1,2,2]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) := h ((lowerBridgeRecords .bPos)[10]'(by decide)) (List.getElem_mem _)
  have h10le := (h10).le
  have h10nle := not_le.mpr h10
  have h11 : lowerWidth ((lowerBridgePair .bPos n k).2++[1,2,2]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1,3,1]) := h ((lowerBridgeRecords .bPos)[11]'(by decide)) (List.getElem_mem _)
  have h11le := (h11).le
  have h11nle := not_le.mpr h11
  have h12 : lowerWidth ((lowerBridgePair .bPos n k).2++[1,2,1]) < lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) := h ((lowerBridgeRecords .bPos)[12]'(by decide)) (List.getElem_mem _)
  have h12le := (h12).le
  have h12nle := not_le.mpr h12
  have h14 : lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) < lowerWidth ((lowerBridgePair .bPos n k).2++[1,2]) := h ((lowerBridgeRecords .bPos)[14]'(by decide)) (List.getElem_mem _)
  have h14le := (h14).le
  have h14nle := not_le.mpr h14
  have h15 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .bPos n k).1++[1,3])++[3]) < lowerWidth (((lowerBridgePair .bPos n k).2++[1,2])++[3]) := h ((lowerBridgeRecords .bPos)[15]'(by decide)) (List.getElem_mem _)
  have h15le := (h15).le
  have h15nle := not_le.mpr h15
  have h17 : lowerWidth ((lowerBridgePair .bPos n k).1++[1,3]) < lowerWidth ((lowerBridgePair .bPos n k).2++[1,2]) := h ((lowerBridgeRecords .bPos)[17]'(by decide)) (List.getElem_mem _)
  have h17le := (h17).le
  have h17nle := not_le.mpr h17
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h0le h0nle h3 h3le h3nle h4 h5 h5le h5nle h6 h6le h6nle h7 h7le h7nle h8 h8le h8nle h10 h10le h10nle h11 h11le h11nle h12 h12le h12nle h14 h14le h14nle h15 h15le h15nle h17 h17le h17nle
  intro e he
  simp only [lowerBridgeEndpoints, lowerBridgeEndpoints_bPos, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [lowerBridgeEndpointFact, lowerBridgeAppend]
    rcases Nat.mod_two_eq_zero_or_one (lowerBridgePair .bPos n k).1.length with hp0 | hp0
    all_goals
      have hp2 : (lowerBridgePair .bPos n k).2.length % 2 = (lowerBridgePair .bPos n k).1.length % 2 := hp.symm
      simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerNormalize, lowerEnds, ends_append, List.suffix_cons_iff, List.length_append,
        hp2, hp0, Nat.add_mod, List.append_assoc, h0, h0le, h0nle, h3, h3le, h3nle, h4, h5, h5le, h5nle, h6, h6le, h6nle, h7, h7le, h7nle, h8, h8le, h8nle, h10, h10le, h10nle, h11, h11le, h11nle, h12, h12le, h12nle, h14, h14le, h14nle, h15, h15le, h15nle, h17, h17le, h17nle]
end OtherBridgeEndpoint

theorem solution (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (h : lowerBridgeFacts c n k) : lowerBridgeEndpointFacts c n k := by
  cases c
  · exact OtherBridgeEndpoint.endpoint_aZero n k h
  · exact OtherBridgeEndpoint.endpoint_aPos n k h
  · exact OtherBridgeEndpoint.endpoint_bZero n k h
  · exact OtherBridgeEndpoint.endpoint_bPos n k h
  · intro e he; simp [lowerBridgeEndpoints, lowerBridgeEndpoints_cZero] at he
  · intro e he; simp [lowerBridgeEndpoints, lowerBridgeEndpoints_cPos] at he
#print axioms solution

example : (∀ (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (h : lowerBridgeFacts c n k) ,  lowerBridgeEndpointFacts c n k) := @solution
