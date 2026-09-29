-- Prove2me | solution 1 for Freiman.trunk_join_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:38:23.291963+00:00
-- url     : https://prove2.me/submissions/bbffde80-9b5e-4dde-895d-f021bf60af42

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

theorem solution (h0 : trunkWitnessBatch 0 125) (h1 : trunkWitnessBatch 125 250) (h2 : trunkWitnessBatch 250 375) (h3 : trunkWitnessBatch 375 500) (h4 : trunkWitnessBatch 500 625) (h5 : trunkWitnessBatch 625 750) (h6 : trunkWitnessBatch 750 875) (h7 : trunkWitnessBatch 875 1000) (h8 : trunkWitnessBatch 1000 1125) (h9 : trunkWitnessBatch 1125 1250) (h10 : trunkWitnessBatch 1250 1375) (h11 : trunkWitnessBatch 1375 1500) (h12 : trunkWitnessBatch 1500 1625) (h13 : trunkWitnessBatch 1625 1750) (h14 : trunkWitnessBatch 1750 1875) (h15 : trunkWitnessBatch 1875 2000) (h16 : trunkWitnessBatch 2000 2125) (h17 : trunkWitnessBatch 2125 2250) (h18 : trunkWitnessBatch 2250 2375) (h19 : trunkWitnessBatch 2375 2500) (h20 : trunkWitnessBatch 2500 2625) (h21 : trunkWitnessBatch 2625 2750) (h22 : trunkWitnessBatch 2750 2875) (h23 : trunkWitnessBatch 2875 3000) (h24 : trunkWitnessBatch 3000 3125) (h25 : trunkWitnessBatch 3125 3250) (h26 : trunkWitnessBatch 3250 3375) (h27 : trunkWitnessBatch 3375 3500) (h28 : trunkWitnessBatch 3500 3625) (h29 : trunkWitnessBatch 3625 3750) (h30 : trunkWitnessBatch 3750 3875) (h31 : trunkWitnessBatch 3875 4000) (h32 : trunkWitnessBatch 4000 4125) (h33 : trunkWitnessBatch 4125 4250) (h34 : trunkWitnessBatch 4250 4375) (h35 : trunkWitnessBatch 4375 4500) (h36 : trunkWitnessBatch 4500 4625) (h37 : trunkWitnessBatch 4625 4750) (h38 : trunkWitnessBatch 4750 4875) (h39 : trunkWitnessBatch 4875 5000) (h40 : trunkWitnessBatch 5000 5125) (h41 : trunkWitnessBatch 5125 5250) (h42 : trunkWitnessBatch 5250 5375) (h43 : trunkWitnessBatch 5375 5500) (h44 : trunkWitnessBatch 5500 5625) (h45 : trunkWitnessBatch 5625 5750) (h46 : trunkWitnessBatch 5750 5875) (h47 : trunkWitnessBatch 5875 6000) (h48 : trunkWitnessBatch 6000 6125) (h49 : trunkWitnessBatch 6125 6250) (h50 : trunkWitnessBatch 6250 6375) (h51 : trunkWitnessBatch 6375 6500) (h52 : trunkWitnessBatch 6500 6625) (h53 : trunkWitnessBatch 6625 6750) (h54 : trunkWitnessBatch 6750 6875) (h55 : trunkWitnessBatch 6875 7000) (h56 : trunkWitnessBatch 7000 7125) (h57 : trunkWitnessBatch 7125 7250) (h58 : trunkWitnessBatch 7250 7375) (h59 : trunkWitnessBatch 7375 7500) (h60 : trunkWitnessBatch 7500 7625) (h61 : trunkWitnessBatch 7625 7750) (h62 : trunkWitnessBatch 7750 7875) (h63 : trunkWitnessBatch 7875 8000) (h64 : trunkWitnessBatch 8000 8125) (h65 : trunkWitnessBatch 8125 8250) (h66 : trunkWitnessBatch 8250 8375) (h67 : trunkWitnessBatch 8375 8500) (h68 : trunkWitnessBatch 8500 8625) (h69 : trunkWitnessBatch 8625 8656) :
    trunkAllWitnesses trunkCatalog := by
  have hs1 : trunkWitnessData01.size = 250 := by decide
  have hs2 : trunkWitnessData02.size = 250 := by decide
  have hs3 : trunkWitnessData03.size = 250 := by decide
  have hs4 : trunkWitnessData04.size = 250 := by decide
  have hs5 : trunkWitnessData05.size = 250 := by decide
  have hs6 : trunkWitnessData06.size = 250 := by decide
  have hs7 : trunkWitnessData07.size = 250 := by decide
  have hs8 : trunkWitnessData08.size = 250 := by decide
  have hs9 : trunkWitnessData09.size = 250 := by decide
  have hs10 : trunkWitnessData10.size = 250 := by decide
  have hs11 : trunkWitnessData11.size = 250 := by decide
  have hs12 : trunkWitnessData12.size = 250 := by decide
  have hs13 : trunkWitnessData13.size = 250 := by decide
  have hs14 : trunkWitnessData14.size = 250 := by decide
  have hs15 : trunkWitnessData15.size = 250 := by decide
  have hs16 : trunkWitnessData16.size = 250 := by decide
  have hs17 : trunkWitnessData17.size = 250 := by decide
  have hs18 : trunkWitnessData18.size = 250 := by decide
  have hs19 : trunkWitnessData19.size = 250 := by decide
  have hs20 : trunkWitnessData20.size = 250 := by decide
  have hs21 : trunkWitnessData21.size = 250 := by decide
  have hs22 : trunkWitnessData22.size = 250 := by decide
  have hs23 : trunkWitnessData23.size = 250 := by decide
  have hs24 : trunkWitnessData24.size = 250 := by decide
  have hs25 : trunkWitnessData25.size = 250 := by decide
  have hs26 : trunkWitnessData26.size = 250 := by decide
  have hs27 : trunkWitnessData27.size = 250 := by decide
  have hs28 : trunkWitnessData28.size = 250 := by decide
  have hs29 : trunkWitnessData29.size = 250 := by decide
  have hs30 : trunkWitnessData30.size = 250 := by decide
  have hs31 : trunkWitnessData31.size = 250 := by decide
  have hs32 : trunkWitnessData32.size = 250 := by decide
  have hs33 : trunkWitnessData33.size = 250 := by decide
  have hs34 : trunkWitnessData34.size = 250 := by decide
  have hs35 : trunkWitnessData35.size = 156 := by decide
  have hsize : trunkCatalog.witnesses.size = 8656 := by
    show trunkDataWitnesses.size = 8656
    simp only [trunkDataWitnesses, Array.size_append, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8,
      hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
      hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31, hs32, hs33, hs34, hs35]
  intro id hpos hle
  have hidlt : id - 1 < 8656 := by omega
  rcases lt_or_ge (id-1) 125 with c0 | c0n
  · have hh := h0 (id-1) (Nat.zero_le _) c0
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 250 with c1 | c1n
  · have hh := h1 (id-1) c0n c1
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 375 with c2 | c2n
  · have hh := h2 (id-1) c1n c2
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 500 with c3 | c3n
  · have hh := h3 (id-1) c2n c3
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 625 with c4 | c4n
  · have hh := h4 (id-1) c3n c4
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 750 with c5 | c5n
  · have hh := h5 (id-1) c4n c5
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 875 with c6 | c6n
  · have hh := h6 (id-1) c5n c6
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1000 with c7 | c7n
  · have hh := h7 (id-1) c6n c7
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1125 with c8 | c8n
  · have hh := h8 (id-1) c7n c8
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1250 with c9 | c9n
  · have hh := h9 (id-1) c8n c9
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1375 with c10 | c10n
  · have hh := h10 (id-1) c9n c10
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1500 with c11 | c11n
  · have hh := h11 (id-1) c10n c11
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1625 with c12 | c12n
  · have hh := h12 (id-1) c11n c12
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1750 with c13 | c13n
  · have hh := h13 (id-1) c12n c13
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 1875 with c14 | c14n
  · have hh := h14 (id-1) c13n c14
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2000 with c15 | c15n
  · have hh := h15 (id-1) c14n c15
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2125 with c16 | c16n
  · have hh := h16 (id-1) c15n c16
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2250 with c17 | c17n
  · have hh := h17 (id-1) c16n c17
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2375 with c18 | c18n
  · have hh := h18 (id-1) c17n c18
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2500 with c19 | c19n
  · have hh := h19 (id-1) c18n c19
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2625 with c20 | c20n
  · have hh := h20 (id-1) c19n c20
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2750 with c21 | c21n
  · have hh := h21 (id-1) c20n c21
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 2875 with c22 | c22n
  · have hh := h22 (id-1) c21n c22
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3000 with c23 | c23n
  · have hh := h23 (id-1) c22n c23
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3125 with c24 | c24n
  · have hh := h24 (id-1) c23n c24
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3250 with c25 | c25n
  · have hh := h25 (id-1) c24n c25
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3375 with c26 | c26n
  · have hh := h26 (id-1) c25n c26
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3500 with c27 | c27n
  · have hh := h27 (id-1) c26n c27
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3625 with c28 | c28n
  · have hh := h28 (id-1) c27n c28
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3750 with c29 | c29n
  · have hh := h29 (id-1) c28n c29
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 3875 with c30 | c30n
  · have hh := h30 (id-1) c29n c30
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4000 with c31 | c31n
  · have hh := h31 (id-1) c30n c31
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4125 with c32 | c32n
  · have hh := h32 (id-1) c31n c32
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4250 with c33 | c33n
  · have hh := h33 (id-1) c32n c33
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4375 with c34 | c34n
  · have hh := h34 (id-1) c33n c34
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4500 with c35 | c35n
  · have hh := h35 (id-1) c34n c35
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4625 with c36 | c36n
  · have hh := h36 (id-1) c35n c36
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4750 with c37 | c37n
  · have hh := h37 (id-1) c36n c37
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 4875 with c38 | c38n
  · have hh := h38 (id-1) c37n c38
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5000 with c39 | c39n
  · have hh := h39 (id-1) c38n c39
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5125 with c40 | c40n
  · have hh := h40 (id-1) c39n c40
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5250 with c41 | c41n
  · have hh := h41 (id-1) c40n c41
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5375 with c42 | c42n
  · have hh := h42 (id-1) c41n c42
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5500 with c43 | c43n
  · have hh := h43 (id-1) c42n c43
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5625 with c44 | c44n
  · have hh := h44 (id-1) c43n c44
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5750 with c45 | c45n
  · have hh := h45 (id-1) c44n c45
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 5875 with c46 | c46n
  · have hh := h46 (id-1) c45n c46
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6000 with c47 | c47n
  · have hh := h47 (id-1) c46n c47
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6125 with c48 | c48n
  · have hh := h48 (id-1) c47n c48
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6250 with c49 | c49n
  · have hh := h49 (id-1) c48n c49
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6375 with c50 | c50n
  · have hh := h50 (id-1) c49n c50
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6500 with c51 | c51n
  · have hh := h51 (id-1) c50n c51
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6625 with c52 | c52n
  · have hh := h52 (id-1) c51n c52
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6750 with c53 | c53n
  · have hh := h53 (id-1) c52n c53
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 6875 with c54 | c54n
  · have hh := h54 (id-1) c53n c54
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7000 with c55 | c55n
  · have hh := h55 (id-1) c54n c55
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7125 with c56 | c56n
  · have hh := h56 (id-1) c55n c56
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7250 with c57 | c57n
  · have hh := h57 (id-1) c56n c57
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7375 with c58 | c58n
  · have hh := h58 (id-1) c57n c58
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7500 with c59 | c59n
  · have hh := h59 (id-1) c58n c59
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7625 with c60 | c60n
  · have hh := h60 (id-1) c59n c60
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7750 with c61 | c61n
  · have hh := h61 (id-1) c60n c61
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 7875 with c62 | c62n
  · have hh := h62 (id-1) c61n c62
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 8000 with c63 | c63n
  · have hh := h63 (id-1) c62n c63
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 8125 with c64 | c64n
  · have hh := h64 (id-1) c63n c64
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 8250 with c65 | c65n
  · have hh := h65 (id-1) c64n c65
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 8375 with c66 | c66n
  · have hh := h66 (id-1) c65n c66
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 8500 with c67 | c67n
  · have hh := h67 (id-1) c66n c67
    rwa [Nat.sub_add_cancel hpos] at hh
  rcases lt_or_ge (id-1) 8625 with c68 | c68n
  · have hh := h68 (id-1) c67n c68
    rwa [Nat.sub_add_cancel hpos] at hh
  have hh := h69 (id-1) c68n (by omega)
  rwa [Nat.sub_add_cancel hpos] at hh
