-- Prove2me | solution 1 for Freiman.trunk_witnesses_0000_0125
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T23:56:26.542097+00:00
-- url     : https://prove2.me/submissions/e206e25e-00a3-47c1-97d9-273533d27f92

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/- trunk_witnesses_0000_0125 : trunkWitnessBatch 0 125 -/

/- Part 1: sizes of the 35 literal witness sub-arrays (each a single,
   non-concatenated array -- decides instantly). -/
theorem hsz01 : trunkWitnessData01.size = 250 := by decide +kernel
theorem hsz02 : trunkWitnessData02.size = 250 := by decide +kernel
theorem hsz03 : trunkWitnessData03.size = 250 := by decide +kernel
theorem hsz04 : trunkWitnessData04.size = 250 := by decide +kernel
theorem hsz05 : trunkWitnessData05.size = 250 := by decide +kernel
theorem hsz06 : trunkWitnessData06.size = 250 := by decide +kernel
theorem hsz07 : trunkWitnessData07.size = 250 := by decide +kernel
theorem hsz08 : trunkWitnessData08.size = 250 := by decide +kernel
theorem hsz09 : trunkWitnessData09.size = 250 := by decide +kernel
theorem hsz10 : trunkWitnessData10.size = 250 := by decide +kernel
theorem hsz11 : trunkWitnessData11.size = 250 := by decide +kernel
theorem hsz12 : trunkWitnessData12.size = 250 := by decide +kernel
theorem hsz13 : trunkWitnessData13.size = 250 := by decide +kernel
theorem hsz14 : trunkWitnessData14.size = 250 := by decide +kernel
theorem hsz15 : trunkWitnessData15.size = 250 := by decide +kernel
theorem hsz16 : trunkWitnessData16.size = 250 := by decide +kernel
theorem hsz17 : trunkWitnessData17.size = 250 := by decide +kernel
theorem hsz18 : trunkWitnessData18.size = 250 := by decide +kernel
theorem hsz19 : trunkWitnessData19.size = 250 := by decide +kernel
theorem hsz20 : trunkWitnessData20.size = 250 := by decide +kernel
theorem hsz21 : trunkWitnessData21.size = 250 := by decide +kernel
theorem hsz22 : trunkWitnessData22.size = 250 := by decide +kernel
theorem hsz23 : trunkWitnessData23.size = 250 := by decide +kernel
theorem hsz24 : trunkWitnessData24.size = 250 := by decide +kernel
theorem hsz25 : trunkWitnessData25.size = 250 := by decide +kernel
theorem hsz26 : trunkWitnessData26.size = 250 := by decide +kernel
theorem hsz27 : trunkWitnessData27.size = 250 := by decide +kernel
theorem hsz28 : trunkWitnessData28.size = 250 := by decide +kernel
theorem hsz29 : trunkWitnessData29.size = 250 := by decide +kernel
theorem hsz30 : trunkWitnessData30.size = 250 := by decide +kernel
theorem hsz31 : trunkWitnessData31.size = 250 := by decide +kernel
theorem hsz32 : trunkWitnessData32.size = 250 := by decide +kernel
theorem hsz33 : trunkWitnessData33.size = 250 := by decide +kernel
theorem hsz34 : trunkWitnessData34.size = 250 := by decide +kernel
theorem hsz35 : trunkWitnessData35.size = 156 := by decide +kernel

/- Part 2: cumulative-size chain (never touches array contents). -/
theorem cum01 : trunkWitnessData01.size = 250 := hsz01
theorem cum02 : (trunkWitnessData01++trunkWitnessData02).size = 500 := by rw [Array.size_append, cum01, hsz02]
theorem cum03 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03).size = 750 := by rw [Array.size_append, cum02, hsz03]
theorem cum04 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04).size = 1000 := by rw [Array.size_append, cum03, hsz04]
theorem cum05 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05).size = 1250 := by rw [Array.size_append, cum04, hsz05]
theorem cum06 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06).size = 1500 := by rw [Array.size_append, cum05, hsz06]
theorem cum07 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07).size = 1750 := by rw [Array.size_append, cum06, hsz07]
theorem cum08 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08).size = 2000 := by rw [Array.size_append, cum07, hsz08]
theorem cum09 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09).size = 2250 := by rw [Array.size_append, cum08, hsz09]
theorem cum10 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10).size = 2500 := by rw [Array.size_append, cum09, hsz10]
theorem cum11 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11).size = 2750 := by rw [Array.size_append, cum10, hsz11]
theorem cum12 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12).size = 3000 := by rw [Array.size_append, cum11, hsz12]
theorem cum13 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13).size = 3250 := by rw [Array.size_append, cum12, hsz13]
theorem cum14 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14).size = 3500 := by rw [Array.size_append, cum13, hsz14]
theorem cum15 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15).size = 3750 := by rw [Array.size_append, cum14, hsz15]
theorem cum16 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16).size = 4000 := by rw [Array.size_append, cum15, hsz16]
theorem cum17 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17).size = 4250 := by rw [Array.size_append, cum16, hsz17]
theorem cum18 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18).size = 4500 := by rw [Array.size_append, cum17, hsz18]
theorem cum19 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19).size = 4750 := by rw [Array.size_append, cum18, hsz19]
theorem cum20 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20).size = 5000 := by rw [Array.size_append, cum19, hsz20]
theorem cum21 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21).size = 5250 := by rw [Array.size_append, cum20, hsz21]
theorem cum22 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22).size = 5500 := by rw [Array.size_append, cum21, hsz22]
theorem cum23 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23).size = 5750 := by rw [Array.size_append, cum22, hsz23]
theorem cum24 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24).size = 6000 := by rw [Array.size_append, cum23, hsz24]
theorem cum25 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25).size = 6250 := by rw [Array.size_append, cum24, hsz25]
theorem cum26 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26).size = 6500 := by rw [Array.size_append, cum25, hsz26]
theorem cum27 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27).size = 6750 := by rw [Array.size_append, cum26, hsz27]
theorem cum28 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28).size = 7000 := by rw [Array.size_append, cum27, hsz28]
theorem cum29 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29).size = 7250 := by rw [Array.size_append, cum28, hsz29]
theorem cum30 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30).size = 7500 := by rw [Array.size_append, cum29, hsz30]
theorem cum31 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31).size = 7750 := by rw [Array.size_append, cum30, hsz31]
theorem cum32 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32).size = 8000 := by rw [Array.size_append, cum31, hsz32]
theorem cum33 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33).size = 8250 := by rw [Array.size_append, cum32, hsz33]
theorem cum34 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33++trunkWitnessData34).size = 8500 := by rw [Array.size_append, cum33, hsz34]
theorem cum35 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33++trunkWitnessData34++trunkWitnessData35).size = 8656 := by rw [Array.size_append, cum34, hsz35]

/- Part 3: locate this leaf's witnesses in sub-array trunkWitnessData01 by directed, one-layer-at-a-time
   Array.getElem?_append_left/_right peels (never a blanket `simp` over the
   whole 35-way concatenation at once -- that blows up combinatorially). -/
theorem hidx (i : ℕ) (hi : i < 125) :
    (trunkDataWitnesses[i + 0]?).getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩ = (trunkWitnessData01[i]?).getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩ := by
  unfold trunkDataWitnesses
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33++trunkWitnessData34).size by rw [cum34]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33).size by rw [cum33]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32).size by rw [cum32]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31).size by rw [cum31]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30).size by rw [cum30]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29).size by rw [cum29]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28).size by rw [cum28]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27).size by rw [cum27]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26).size by rw [cum26]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25).size by rw [cum25]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24).size by rw [cum24]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23).size by rw [cum23]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22).size by rw [cum22]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21).size by rw [cum21]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20).size by rw [cum20]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19).size by rw [cum19]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18).size by rw [cum18]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17).size by rw [cum17]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16).size by rw [cum16]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15).size by rw [cum15]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14).size by rw [cum14]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13).size by rw [cum13]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12).size by rw [cum12]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11).size by rw [cum11]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10).size by rw [cum10]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09).size by rw [cum09]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08).size by rw [cum08]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07).size by rw [cum07]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06).size by rw [cum06]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05).size by rw [cum05]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04).size by rw [cum04]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03).size by rw [cum03]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < (trunkWitnessData01++trunkWitnessData02).size by rw [cum02]; omega)]
  rw [Array.getElem?_append_left (show i + 0 < trunkWitnessData01.size by rw [cum01]; omega)]
  rfl

/- Part 4: the coefficients-equality conjunct of `certWitnessValid` is TRUE BY
   CONSTRUCTION for every `trunkPairWitness` -- proved once, generically. -/
theorem coeffEq_rfl (C : TrunkCatalog) (w : TrunkWitness) :
    (trunkPairWitness C w).coefficients =
      certBernsteinCoefficients
        (certCrossPolynomial (trunkPairWitness C w).lowerBound.threshold
          (trunkPairWitness C w).upperBound.threshold) (trunkPairWitness C w).rectangle := by
  rfl

/- Part 5: remaining witness-specific content of `trunkWitnessValid`
   (everything except `coeffEq_rfl` above and except the diag/id-range checks,
   which are folded in here too so one `decide +kernel` per chunk suffices). -/
def fullCheck (C : TrunkCatalog) (w : TrunkWitness) : Prop :=
  w.diagonal = 0 ∧
  0 < w.lowerId ∧ w.lowerId ≤ C.bounds.size ∧ 0 < w.upperId ∧ w.upperId ≤ C.bounds.size ∧
  (trunkPairWitness C w).lowerBound.lower = true ∧ (trunkPairWitness C w).upperBound.lower = false ∧
  certRectangleValid (trunkPairWitness C w).rectangle ∧ 0 ≤ (trunkPairWitness C w).rectangle.r0 ∧
  certThresholdDataValid (trunkPairWitness C w).lowerBound.threshold ∧
  certThresholdDataValid (trunkPairWitness C w).upperBound.threshold ∧
  (∀ i j : Fin 3, certCoefficientBoundValid ((trunkPairWitness C w).coefficients i j)
    ((trunkPairWitness C w).lowerBounds i j)) ∧
  ((∀ i j : Fin 3, 0 < (trunkPairWitness C w).lowerBounds i j) ∨
    (trunkPairWitness C w).lowerBound.strict = true ∨ (trunkPairWitness C w).upperBound.strict = true)

theorem fullCheck_imp {C : TrunkCatalog} {w : TrunkWitness} (h : fullCheck C w) :
    trunkWitnessValid C w := by
  obtain ⟨hd,h1,h2,h3,h4,f1,f2,f3,f4,f5,f6,f8,f9⟩ := h
  unfold trunkWitnessValid
  rw [if_pos hd]
  exact ⟨h1,h2,h3,h4,f1,f2,f3,f4,f5,f6, coeffEq_rfl C w, f8, f9⟩

theorem chunk_mem {s n j : ℕ} (h1 : s ≤ j) (h2 : j < s + n) : j ∈ List.range' s n :=
  List.mem_range'_1.mpr ⟨h1, h2⟩

/- Part 6: the actual certificate checks, chunked into two halves to bound
   kernel memory/GC overhead. -/
theorem keyA : ∀ j ∈ List.range' 0 62,
    fullCheck trunkCatalog (trunkWitnessData01[j]?.getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩) := by
  unfold fullCheck certRectangleValid certThresholdDataValid certCoefficientBoundValid
  decide +kernel

theorem keyB : ∀ j ∈ List.range' 62 63,
    fullCheck trunkCatalog (trunkWitnessData01[j]?.getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩) := by
  unfold fullCheck certRectangleValid certThresholdDataValid certCoefficientBoundValid
  decide +kernel

theorem key : ∀ j ∈ List.range' 0 125,
    trunkWitnessValid trunkCatalog (trunkWitnessData01[j]?.getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩) := by
  intro j hj
  simp only [List.mem_range'_1] at hj
  rcases (show (0 ≤ j ∧ j < 62) ∨ (62 ≤ j ∧ j < 125) by omega) with h | h
  · exact fullCheck_imp (keyA j (chunk_mem h.1 h.2))
  · exact fullCheck_imp (keyB j (chunk_mem h.1 h.2))

theorem solution : trunkWitnessBatch 0 125 := by
  intro i hlo hhi
  have heq : trunkWitness trunkCatalog (i+1) = trunkWitnessData01[i - 0]?.getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩ := by
    unfold trunkWitness
    simp only [Nat.add_sub_cancel]
    show trunkCatalog.witnesses[i]?.getD _ = _
    rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl]
    have := hidx (i - 0) (show i - 0 < 125 by omega)
    rwa [show i - 0 + 0 = i by omega] at this
  rw [heq]
  have hj : i - 0 ∈ List.range' 0 125 := chunk_mem (by omega) (by omega)
  exact key (i - 0) hj
