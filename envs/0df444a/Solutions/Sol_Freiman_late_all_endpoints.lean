-- Prove2me | solution 1 for Freiman.late_all_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-09-16T00:44:22.245128+00:00
-- url     : https://prove2.me/submissions/0b4388b3-e757-4b17-8794-165009410135

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance (i n : ℕ) : Decidable (lateIndex i n) := by
  unfold lateIndex
  infer_instance

instance (C : LateCatalog) (ids : List ℕ) : Decidable (lateIndices C ids) := by
  unfold lateIndices
  infer_instance

private theorem endpoint_cases_iff (es : List LowerHistoryEndCase)
    (v : CertField × CertField) (bs : List CertBound) :
    (∃ cs, (v,cs) ∈ es ∧ cs.toFinset = bs.toFinset) ↔
    ∃ e ∈ es, e.1 = v ∧ e.2.toFinset = bs.toFinset := by
  constructor
  · rintro ⟨cs, hm, he⟩
    exact ⟨(v,cs), hm, rfl, he⟩
  · rintro ⟨⟨w,cs⟩, hm, he, hb⟩
    cases he
    exact ⟨cs, hm, hb⟩

instance (C : LateCatalog) (e : LateEndpoint) : Decidable (lateEndpointValid C e) := by
  unfold lateEndpointValid
  haveI (ids : List ℕ) : Decidable
      (∃ cs, (e.value,cs) ∈ lateEndpointCases e.right3 e.words e.upper ∧
        cs.toFinset = (lateBounds C ids).toFinset) :=
    decidable_of_iff
      (∃ z ∈ lateEndpointCases e.right3 e.words e.upper,
        z.1 = e.value ∧ z.2.toFinset = (lateBounds C ids).toFinset)
      (endpoint_cases_iff _ _ _).symm
  infer_instance


private theorem ep1 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 1) := by
  decide +kernel

private theorem ep2 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 2) := by
  decide +kernel

private theorem ep3 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 3) := by
  decide +kernel

private theorem ep4 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 4) := by
  decide +kernel

private theorem ep5 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 5) := by
  decide +kernel

private theorem ep6 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 6) := by
  decide +kernel

private theorem ep7 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 7) := by
  decide +kernel

private theorem ep8 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 8) := by
  decide +kernel

private theorem ep9 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 9) := by
  decide +kernel

private theorem ep10 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 10) := by
  decide +kernel

private theorem ep11 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 11) := by
  decide +kernel

private theorem ep12 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 12) := by
  decide +kernel

private theorem ep13 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 13) := by
  decide +kernel

private theorem ep14 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 14) := by
  decide +kernel

private theorem ep15 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 15) := by
  decide +kernel

private theorem ep16 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 16) := by
  decide +kernel

private theorem ep17 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 17) := by
  decide +kernel

private theorem ep18 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 18) := by
  decide +kernel

private theorem ep19 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 19) := by
  decide +kernel

private theorem ep20 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 20) := by
  decide +kernel

private theorem ep21 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 21) := by
  decide +kernel

private theorem ep22 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 22) := by
  decide +kernel

private theorem ep23 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 23) := by
  decide +kernel

private theorem ep24 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 24) := by
  decide +kernel

private theorem ep25 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 25) := by
  decide +kernel

private theorem ep26 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 26) := by
  decide +kernel

private theorem ep27 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 27) := by
  decide +kernel

private theorem ep28 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 28) := by
  decide +kernel

private theorem ep29 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 29) := by
  decide +kernel

private theorem ep30 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 30) := by
  decide +kernel

private theorem ep31 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 31) := by
  decide +kernel

private theorem ep32 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 32) := by
  decide +kernel

private theorem ep33 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 33) := by
  decide +kernel

private theorem ep34 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 34) := by
  decide +kernel

private theorem ep35 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 35) := by
  decide +kernel

private theorem ep36 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 36) := by
  decide +kernel

private theorem ep37 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 37) := by
  decide +kernel

private theorem ep38 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 38) := by
  decide +kernel

private theorem ep39 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 39) := by
  decide +kernel

private theorem ep40 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 40) := by
  decide +kernel

private theorem ep41 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 41) := by
  decide +kernel

private theorem ep42 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 42) := by
  decide +kernel

private theorem ep43 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 43) := by
  decide +kernel

private theorem ep44 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 44) := by
  decide +kernel

private theorem ep45 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 45) := by
  decide +kernel

private theorem ep46 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 46) := by
  decide +kernel

private theorem ep47 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 47) := by
  decide +kernel

private theorem ep48 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 48) := by
  decide +kernel

private theorem ep49 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 49) := by
  decide +kernel

private theorem ep50 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 50) := by
  decide +kernel

private theorem ep51 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 51) := by
  decide +kernel

private theorem ep52 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 52) := by
  decide +kernel

private theorem ep53 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 53) := by
  decide +kernel

private theorem ep54 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 54) := by
  decide +kernel

private theorem ep55 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 55) := by
  decide +kernel

private theorem ep56 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 56) := by
  decide +kernel

private theorem ep57 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 57) := by
  decide +kernel

private theorem ep58 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 58) := by
  decide +kernel

private theorem ep59 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 59) := by
  decide +kernel

private theorem ep60 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 60) := by
  decide +kernel

private theorem ep61 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 61) := by
  decide +kernel

private theorem ep62 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 62) := by
  decide +kernel

private theorem ep63 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 63) := by
  decide +kernel

private theorem ep64 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 64) := by
  decide +kernel

private theorem ep65 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 65) := by
  decide +kernel

private theorem ep66 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 66) := by
  decide +kernel

private theorem ep67 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 67) := by
  decide +kernel

private theorem ep68 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 68) := by
  decide +kernel

private theorem ep69 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 69) := by
  decide +kernel

private theorem ep70 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 70) := by
  decide +kernel

private theorem ep71 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 71) := by
  decide +kernel

private theorem ep72 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 72) := by
  decide +kernel

private theorem ep73 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 73) := by
  decide +kernel

private theorem ep74 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 74) := by
  decide +kernel

private theorem ep75 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 75) := by
  decide +kernel

private theorem ep76 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 76) := by
  decide +kernel

private theorem ep77 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 77) := by
  decide +kernel

private theorem ep78 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 78) := by
  decide +kernel

private theorem ep79 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 79) := by
  decide +kernel

private theorem ep80 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 80) := by
  decide +kernel

private theorem ep81 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 81) := by
  decide +kernel

private theorem ep82 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 82) := by
  decide +kernel

private theorem ep83 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 83) := by
  decide +kernel

private theorem ep84 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 84) := by
  decide +kernel

private theorem ep85 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 85) := by
  decide +kernel

private theorem ep86 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 86) := by
  decide +kernel

private theorem ep87 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 87) := by
  decide +kernel

private theorem ep88 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 88) := by
  decide +kernel

private theorem ep89 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 89) := by
  decide +kernel

private theorem ep90 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 90) := by
  decide +kernel

private theorem ep91 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 91) := by
  decide +kernel

private theorem ep92 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 92) := by
  decide +kernel

private theorem ep93 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 93) := by
  decide +kernel

private theorem ep94 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 94) := by
  decide +kernel

private theorem ep95 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 95) := by
  decide +kernel

private theorem ep96 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 96) := by
  decide +kernel

private theorem ep97 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 97) := by
  decide +kernel

private theorem ep98 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 98) := by
  decide +kernel

private theorem ep99 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 99) := by
  decide +kernel

private theorem ep100 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 100) := by
  decide +kernel

private theorem ep101 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 101) := by
  decide +kernel

private theorem ep102 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 102) := by
  decide +kernel

private theorem ep103 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 103) := by
  decide +kernel

private theorem ep104 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 104) := by
  decide +kernel

private theorem ep105 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 105) := by
  decide +kernel

private theorem ep106 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 106) := by
  decide +kernel

private theorem ep107 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 107) := by
  decide +kernel

private theorem ep108 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 108) := by
  decide +kernel

private theorem ep109 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 109) := by
  decide +kernel

private theorem ep110 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 110) := by
  decide +kernel

private theorem ep111 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 111) := by
  decide +kernel

private theorem ep112 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 112) := by
  decide +kernel

private theorem ep113 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 113) := by
  decide +kernel

private theorem ep114 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 114) := by
  decide +kernel

private theorem ep115 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 115) := by
  decide +kernel

private theorem ep116 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 116) := by
  decide +kernel

private theorem ep117 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 117) := by
  decide +kernel

private theorem ep118 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 118) := by
  decide +kernel

private theorem ep119 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 119) := by
  decide +kernel

private theorem ep120 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 120) := by
  decide +kernel

private theorem ep121 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 121) := by
  decide +kernel

private theorem ep122 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 122) := by
  decide +kernel

private theorem ep123 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 123) := by
  decide +kernel

private theorem ep124 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 124) := by
  decide +kernel

private theorem ep125 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 125) := by
  decide +kernel

private theorem ep126 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 126) := by
  decide +kernel

private theorem ep127 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 127) := by
  decide +kernel

private theorem ep128 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 128) := by
  decide +kernel

private theorem ep129 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 129) := by
  decide +kernel

private theorem ep130 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 130) := by
  decide +kernel

private theorem ep131 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 131) := by
  decide +kernel

private theorem ep132 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 132) := by
  decide +kernel

private theorem ep133 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 133) := by
  decide +kernel

private theorem ep134 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 134) := by
  decide +kernel

private theorem ep135 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 135) := by
  decide +kernel

private theorem ep136 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 136) := by
  decide +kernel

private theorem ep137 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 137) := by
  decide +kernel

private theorem ep138 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 138) := by
  decide +kernel

private theorem ep139 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 139) := by
  decide +kernel

private theorem ep140 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 140) := by
  decide +kernel

private theorem ep141 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 141) := by
  decide +kernel

private theorem ep142 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 142) := by
  decide +kernel

private theorem ep143 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 143) := by
  decide +kernel

private theorem ep144 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 144) := by
  decide +kernel

private theorem ep145 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 145) := by
  decide +kernel

private theorem ep146 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 146) := by
  decide +kernel

private theorem ep147 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 147) := by
  decide +kernel

private theorem ep148 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 148) := by
  decide +kernel

private theorem ep149 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 149) := by
  decide +kernel

private theorem ep150 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 150) := by
  decide +kernel

private theorem ep151 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 151) := by
  decide +kernel

private theorem ep152 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 152) := by
  decide +kernel

private theorem ep153 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 153) := by
  decide +kernel

private theorem ep154 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 154) := by
  decide +kernel

private theorem ep155 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 155) := by
  decide +kernel

private theorem ep156 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 156) := by
  decide +kernel

private theorem ep157 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 157) := by
  decide +kernel

private theorem ep158 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 158) := by
  decide +kernel

private theorem ep159 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 159) := by
  decide +kernel

private theorem ep160 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 160) := by
  decide +kernel

private theorem ep161 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 161) := by
  decide +kernel

private theorem ep162 : lateEndpointValid lateCatalog (lateEndpoint lateCatalog 162) := by
  decide +kernel

theorem solution : lateAllEndpoints lateCatalog := by
  intro i hi
  have hs : lateCatalog.endpoints.size = 162 := by decide
  have hr : 0 < i ∧ i ≤ 162 := by simpa only [lateIndex, hs] using hi
  rcases hr with ⟨h0, h162⟩
  interval_cases i
  · exact ep1
  · exact ep2
  · exact ep3
  · exact ep4
  · exact ep5
  · exact ep6
  · exact ep7
  · exact ep8
  · exact ep9
  · exact ep10
  · exact ep11
  · exact ep12
  · exact ep13
  · exact ep14
  · exact ep15
  · exact ep16
  · exact ep17
  · exact ep18
  · exact ep19
  · exact ep20
  · exact ep21
  · exact ep22
  · exact ep23
  · exact ep24
  · exact ep25
  · exact ep26
  · exact ep27
  · exact ep28
  · exact ep29
  · exact ep30
  · exact ep31
  · exact ep32
  · exact ep33
  · exact ep34
  · exact ep35
  · exact ep36
  · exact ep37
  · exact ep38
  · exact ep39
  · exact ep40
  · exact ep41
  · exact ep42
  · exact ep43
  · exact ep44
  · exact ep45
  · exact ep46
  · exact ep47
  · exact ep48
  · exact ep49
  · exact ep50
  · exact ep51
  · exact ep52
  · exact ep53
  · exact ep54
  · exact ep55
  · exact ep56
  · exact ep57
  · exact ep58
  · exact ep59
  · exact ep60
  · exact ep61
  · exact ep62
  · exact ep63
  · exact ep64
  · exact ep65
  · exact ep66
  · exact ep67
  · exact ep68
  · exact ep69
  · exact ep70
  · exact ep71
  · exact ep72
  · exact ep73
  · exact ep74
  · exact ep75
  · exact ep76
  · exact ep77
  · exact ep78
  · exact ep79
  · exact ep80
  · exact ep81
  · exact ep82
  · exact ep83
  · exact ep84
  · exact ep85
  · exact ep86
  · exact ep87
  · exact ep88
  · exact ep89
  · exact ep90
  · exact ep91
  · exact ep92
  · exact ep93
  · exact ep94
  · exact ep95
  · exact ep96
  · exact ep97
  · exact ep98
  · exact ep99
  · exact ep100
  · exact ep101
  · exact ep102
  · exact ep103
  · exact ep104
  · exact ep105
  · exact ep106
  · exact ep107
  · exact ep108
  · exact ep109
  · exact ep110
  · exact ep111
  · exact ep112
  · exact ep113
  · exact ep114
  · exact ep115
  · exact ep116
  · exact ep117
  · exact ep118
  · exact ep119
  · exact ep120
  · exact ep121
  · exact ep122
  · exact ep123
  · exact ep124
  · exact ep125
  · exact ep126
  · exact ep127
  · exact ep128
  · exact ep129
  · exact ep130
  · exact ep131
  · exact ep132
  · exact ep133
  · exact ep134
  · exact ep135
  · exact ep136
  · exact ep137
  · exact ep138
  · exact ep139
  · exact ep140
  · exact ep141
  · exact ep142
  · exact ep143
  · exact ep144
  · exact ep145
  · exact ep146
  · exact ep147
  · exact ep148
  · exact ep149
  · exact ep150
  · exact ep151
  · exact ep152
  · exact ep153
  · exact ep154
  · exact ep155
  · exact ep156
  · exact ep157
  · exact ep158
  · exact ep159
  · exact ep160
  · exact ep161
  · exact ep162

#print axioms solution
