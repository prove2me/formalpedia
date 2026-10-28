-- Prove2me | solution 1 for BitDFT.shared_alphabet_core_symbols
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:19:12.689683+00:00
-- url     : https://prove2.me/submissions/a1ba6285-d9f1-4bbb-bcde-7d43e33a641c

import Definitions.Def_BitDFT_SharedAlphabet

set_option autoImplicit false
open IntMul BitDFT.SharedAlphabet

/-- The distinguished tape symbols have identical product encodings in both
    component embeddings, so binary packets can pass between the stages. -/
theorem solution (A M : MultitapeTM) :
    (left A M).encode A.blank = (right A M).encode M.blank ∧
    (left A M).encode A.startSym = (right A M).encode M.startSym ∧
    (left A M).encode A.zero = (right A M).encode M.zero ∧
    (left A M).encode A.one = (right A M).encode M.one ∧
    (left A M).encode A.sep = (right A M).encode M.sep ∧
    (∀ b : Bool, (left A M).encode (A.bitSym b) = (right A M).encode (M.bitSym b)) := by
  have hA := A.syms_distinct
  simp [List.nodup_cons,List.mem_cons,not_or] at hA
  rcases hA with ⟨⟨a01,a02,a03,a04⟩,⟨a12,a13,a14⟩,⟨a23,a24⟩,a34⟩
  have hM := M.syms_distinct
  simp [List.nodup_cons,List.mem_cons,not_or] at hM
  rcases hM with ⟨⟨m01,m02,m03,m04⟩,⟨m12,m13,m14⟩,⟨m23,m24⟩,m34⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [left,right,mate,Ne.symm a01,Ne.symm a02,Ne.symm a03,Ne.symm a04,Ne.symm a12,
      Ne.symm a13,Ne.symm a14,Ne.symm a23,Ne.symm a24,Ne.symm a34,
      Ne.symm m01,Ne.symm m02,Ne.symm m03,Ne.symm m04,Ne.symm m12,
      Ne.symm m13,Ne.symm m14,Ne.symm m23,Ne.symm m24,Ne.symm m34]
  · simp [left,right,mate,Ne.symm a01,Ne.symm a02,Ne.symm a03,Ne.symm a04,Ne.symm a12,
      Ne.symm a13,Ne.symm a14,Ne.symm a23,Ne.symm a24,Ne.symm a34,
      Ne.symm m01,Ne.symm m02,Ne.symm m03,Ne.symm m04,Ne.symm m12,
      Ne.symm m13,Ne.symm m14,Ne.symm m23,Ne.symm m24,Ne.symm m34]
  · simp [left,right,mate,Ne.symm a01,Ne.symm a02,Ne.symm a03,Ne.symm a04,Ne.symm a12,
      Ne.symm a13,Ne.symm a14,Ne.symm a23,Ne.symm a24,Ne.symm a34,
      Ne.symm m01,Ne.symm m02,Ne.symm m03,Ne.symm m04,Ne.symm m12,
      Ne.symm m13,Ne.symm m14,Ne.symm m23,Ne.symm m24,Ne.symm m34]
  · simp [left,right,mate,Ne.symm a01,Ne.symm a02,Ne.symm a03,Ne.symm a04,Ne.symm a12,
      Ne.symm a13,Ne.symm a14,Ne.symm a23,Ne.symm a24,Ne.symm a34,
      Ne.symm m01,Ne.symm m02,Ne.symm m03,Ne.symm m04,Ne.symm m12,
      Ne.symm m13,Ne.symm m14,Ne.symm m23,Ne.symm m24,Ne.symm m34]
  · simp [left,right,mate,Ne.symm a01,Ne.symm a02,Ne.symm a03,Ne.symm a04,Ne.symm a12,
      Ne.symm a13,Ne.symm a14,Ne.symm a23,Ne.symm a24,Ne.symm a34,
      Ne.symm m01,Ne.symm m02,Ne.symm m03,Ne.symm m04,Ne.symm m12,
      Ne.symm m13,Ne.symm m14,Ne.symm m23,Ne.symm m24,Ne.symm m34]
  · intro b
    cases b <;> simp [left,right,mate,MultitapeTM.bitSym,Ne.symm a01,Ne.symm a02,Ne.symm a03,Ne.symm a04,Ne.symm a12,
      Ne.symm a13,Ne.symm a14,Ne.symm a23,Ne.symm a24,Ne.symm a34,
      Ne.symm m01,Ne.symm m02,Ne.symm m03,Ne.symm m04,Ne.symm m12,
      Ne.symm m13,Ne.symm m14,Ne.symm m23,Ne.symm m24,Ne.symm m34]
