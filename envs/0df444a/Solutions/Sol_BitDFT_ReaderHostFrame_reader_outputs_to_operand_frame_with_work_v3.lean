-- Prove2me | solution 1 for BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame_with_work_v3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:10:01.076505+00:00
-- url     : https://prove2.me/submissions/7ece641c-8ee7-4b2d-aeaa-aebda485c793

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem solution (A M H : MultitapeTM)
    (hH4 : 3 < H.k) (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k)
    (hj : 1 ≤ j.val) (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1) :
    ∃ base : (BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells (BankedOperandStage.dimensionTape A M H) =
        (host A M H).tapeOf (dimension.map (host A M H).bitSym) ∧
      base.head (BankedOperandStage.dimensionTape A M H) = dimension.length + 1 ∧
      base.cells (BankedOperandStage.coordinateTape A M H j) =
        (host A M H).tapeOf (([sign, high] ++ low).map (host A M H).bitSym) ∧
      base.head (BankedOperandStage.coordinateTape A M H j) = low.length + 3 ∧
      ∀ i : Fin (tracked M).k, 2 ≤ i.val →
        base.cells (multiplierTapeRoute A M H i) = (host A M H).tapeOf [] ∧
        base.head (multiplierTapeRoute A M H i) = 1 := by
  let N := host A M H
  let eH := TripleAlphabet.header A (tracked M) H
  let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
  have hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
    dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
    have hA := A.two_le_k
    have hM := (tracked M).two_le_k
    have hH := H.two_le_k
    omega
  have hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k
    have hM := (tracked M).two_le_k
    have hH := H.two_le_k
    omega
  let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH
  let coord := BankedOperandStage.coordinateTape A M H j
  let dim := BankedOperandStage.dimensionTape A M H
  let base : (BankedOperandStage.controller A M H j hj).machine.Cfg :=
    ⟨OperandStage.State.skipSign, cfg.cells,
      fun t => if t.val = coord.val then low.length + 3 else cfg.head t⟩
  have hcoordinate := header_frame_keeps_fourier_tape A M H cF cH j hj coord rfl
  have hdimension := header_frame_dimension_projection A M H hH4 cF cH
  have hdimEnc : cfg.cells dim = N.tapeOf (dimension.map N.bitSym) := by
    have hraw := hdimension.1
    change cfg.cells dim = (fun p => eH.encode (cH.cells ⟨3, hH4⟩ p)) at hraw
    rw [hdim] at hraw
    have hT := hraw.trans (encode_tapeOf_bits eH dimension)
    change cfg.cells dim = (BankedTripleAlphabetHost.carrier A (tracked M) H).tapeOf
      (dimension.map (BankedTripleAlphabetHost.carrier A (tracked M) H).bitSym)
    exact hT
  have hcoordEnc : cfg.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) := by
    have hraw := hcoordinate.1
    have hraw' : cfg.cells coord = (fun x => (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells j x)) := by
      simpa [coord] using hraw
    rw [hcoord] at hraw'
    have hT := hraw'.trans (encode_tapeOf_bits (TripleAlphabet.fourier A (tracked M) H)
      ([sign, high] ++ low))
    change cfg.cells coord = (BankedTripleAlphabetHost.carrier A (tracked M) H).tapeOf
      (([sign, high] ++ low).map (BankedTripleAlphabetHost.carrier A (tracked M) H).bitSym)
    simpa [List.map_append] using hT
  have hdimHeadCfg : cfg.head dim = dimension.length + 1 := by
    have hraw := hdimension.2
    change cfg.head dim = cH.head ⟨3, hH4⟩ at hraw
    rw [hdimHead] at hraw
    exact hraw
  have hcoordHeadCfg : cfg.head coord = cF.head j := by
    have hraw := hcoordinate.2
    simpa [coord] using hraw
  have hdimBase : base.cells dim = N.tapeOf (dimension.map N.bitSym) := hdimEnc
  have hcoordBase : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) := hcoordEnc
  have hdimBaseHead : base.head dim = dimension.length + 1 := by
    have hne : coord ≠ dim := BankedOperandStage.coordinate_ne_dimension A M H j
    have hneVal : coord.val ≠ dim.val := fun hv => hne (Fin.ext hv)
    change (if dim.val = coord.val then low.length + 3 else cfg.head dim) = _
    rw [if_neg (fun hv => hneVal hv.symm)]
    exact hdimHeadCfg
  have hcoordBaseHead : base.head coord = low.length + 3 := by
    change (if coord.val = coord.val then low.length + 3 else cfg.head coord) = _
    simp
  have hwork : ∀ i : Fin (tracked M).k, 2 ≤ i.val →
      base.cells (multiplierTapeRoute A M H i) = N.tapeOf [] ∧
      base.head (multiplierTapeRoute A M H i) = 1 := by
    intro i hi
    let Rm := multiplierTapeRoute A M H
    let Rh := headerRoute A M H
    let Rf := fourierRoute A M H
    let p := Rm i
    have hmul : p.val = A.k + i.val - 1 := by
      have h := DedicatedTapeBanks.multiplier_work_address A (tracked M) H i (by omega)
      have h' := congrArg Fin.val h
      simpa [p, Rm, multiplierTapeRoute, BankedTripleAlphabetHost.route,
        TapeExtension.oldTape, Fin.cast] using h'
    have hpLower : A.k + 1 ≤ p.val := by omega
    have hHeaderExtra : H.k ≤ (Rh.symm p).val := by
      by_contra hnot
      have hlt : (Rh.symm p).val < H.k := Nat.lt_of_not_ge hnot
      let q := Rh.symm p
      have hroute : Rh q = p := Equiv.apply_symm_apply Rh p
      by_cases hq0 : q.val = 0
      · have hqEq : q = ⟨0, by omega⟩ := Fin.ext hq0
        have hinput := DedicatedTapeBanks.routing_input (DedicatedTapeBanks.tail A (tracked M) H)
          (DedicatedTapeBanks.headerOffset A (tracked M) H)
          (by
            have hA := A.two_le_k
            have hM := (tracked M).two_le_k
            have hH := H.two_le_k
            dsimp [DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
            omega)
        have hroute0 : Rh q = ⟨0, by omega⟩ := by
          rw [hqEq]
          simpa [Rh, headerRoute, BankedTripleAlphabetHost.route] using hinput
        have hp0 := congrArg Fin.val (hroute.symm.trans hroute0)
        omega
      · have hqpos : 1 ≤ q.val := by omega
        have hend : DedicatedTapeBanks.headerOffset A (tracked M) H + q.val <
            DedicatedTapeBanks.width A (tracked M) H := by
          rw [DedicatedTapeBanks.width_eq_sum]
          dsimp [DedicatedTapeBanks.headerOffset]
          omega
        have hqaddr := DedicatedTapeBanks.routing_work (DedicatedTapeBanks.tail A (tracked M) H)
          (DedicatedTapeBanks.headerOffset A (tracked M) H)
          (by
            have hA := A.two_le_k
            have hM := (tracked M).two_le_k
            have hH := H.two_le_k
            dsimp [DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
            omega) q hqpos hend
        have hqval := congrArg Fin.val hqaddr
        have hrelval := congrArg Fin.val hroute
        have hqval' : p.val = A.k + (tracked M).k + q.val - 2 := by
          have haddrval : (Rh q).val = A.k + (tracked M).k + q.val - 2 := by
            dsimp [Rh, headerRoute, BankedTripleAlphabetHost.route,
              DedicatedTapeBanks.headerOffset] at hqval ⊢
            omega
          omega
        omega
    have hFourierExtra : A.k ≤ (Rf.symm p).val := by
      by_contra hnot
      have hlt : (Rf.symm p).val < A.k := Nat.lt_of_not_ge hnot
      let q := Rf.symm p
      have hroute : Rf q = p := Equiv.apply_symm_apply Rf p
      by_cases hq0 : q.val = 0
      · have hqEq : q = ⟨0, by omega⟩ := Fin.ext hq0
        have hinput := DedicatedTapeBanks.routing_input (DedicatedTapeBanks.tail A (tracked M) H)
          (DedicatedTapeBanks.fourierOffset A (tracked M) H)
          (by
            have hA := A.two_le_k
            have hM := (tracked M).two_le_k
            have hH := H.two_le_k
            dsimp [DedicatedTapeBanks.fourierOffset, DedicatedTapeBanks.tail]
            omega)
        have hroute0 : Rf q = ⟨0, by omega⟩ := by
          rw [hqEq]
          simpa [Rf, fourierRoute, BankedTripleAlphabetHost.route] using hinput
        have hp0 := congrArg Fin.val (hroute.symm.trans hroute0)
        omega
      · have hqpos : 1 ≤ q.val := by omega
        have hend : DedicatedTapeBanks.fourierOffset A (tracked M) H + q.val <
            5 + DedicatedTapeBanks.tail A (tracked M) H := by
          simpa [DedicatedTapeBanks.fourierOffset] using q.isLt
        have hqaddr := DedicatedTapeBanks.routing_work (DedicatedTapeBanks.tail A (tracked M) H)
          (DedicatedTapeBanks.fourierOffset A (tracked M) H)
          (by
            have hA := A.two_le_k
            have hM := (tracked M).two_le_k
            have hH := H.two_le_k
            dsimp [DedicatedTapeBanks.fourierOffset, DedicatedTapeBanks.tail]
            omega) q hqpos hend
        have hqval := congrArg Fin.val hqaddr
        have hrelval := congrArg Fin.val hroute
        have hqval' : p.val = q.val := by
          have haddrval : (Rf q).val = q.val := by
            simpa [Rf, fourierRoute, BankedTripleAlphabetHost.route,
              DedicatedTapeBanks.fourierOffset] using hqval
          omega
        omega
    have hExtra := BankedTripleAlphabetHost.config_extra_tape A (tracked M) H H eH hoff hhoff hX
      (parkedCells A M H cF) (parkedHeads A M H cF) cH (Rh.symm p) hHeaderExtra
    have hcfgCells : cfg.cells p = parkedCells A M H cF p := by
      simpa [cfg, Rh, headerRoute, hoff] using hExtra.1
    have hcfgHead : cfg.head p = parkedHeads A M H cF p := by
      simpa [cfg, Rh, headerRoute, hoff] using hExtra.2
    have hFneg : ¬ ((fourierRoute A M H).symm p).val < A.k := by
      change ¬ (Rf.symm p).val < A.k
      omega
    have hparkCells : parkedCells A M H cF p = N.tapeOf [] := by
      funext x
      change (if h : ((fourierRoute A M H).symm p).val < A.k then
        (TripleAlphabet.fourier A (tracked M) H).encode
          (cF.cells ⟨((fourierRoute A M H).symm p).val, h⟩ x)
        else if x = 0 then (BankedTripleAlphabetHost.carrier A (tracked M) H).startSym
          else (BankedTripleAlphabetHost.carrier A (tracked M) H).blank) =
          (BankedTripleAlphabetHost.carrier A (tracked M) H).tapeOf [] x
      simp only [dif_neg hFneg]
      by_cases hx : x = 0
      · subst x
        simp [MultitapeTM.tapeOf]
      · cases x with
        | zero => exact (hx rfl).elim
        | succ n => rfl
    have hparkHead : parkedHeads A M H cF p = 1 := by
      change (if h : ((fourierRoute A M H).symm p).val < A.k then
        cF.head ⟨((fourierRoute A M H).symm p).val, h⟩ else 1) = 1
      simp only [dif_neg hFneg]
    have hcoordNe : p.val ≠ coord.val := by
      have hjlt := j.isLt
      have hcoordVal : coord.val = j.val := by rfl
      omega
    have hcells : base.cells p = N.tapeOf [] := by
      change cfg.cells p = N.tapeOf []
      rw [hcfgCells, hparkCells]
    have hheads : base.head p = 1 := by
      change (if p.val = coord.val then low.length + 3 else cfg.head p) = 1
      rw [if_neg hcoordNe]
      rw [hcfgHead, hparkHead]
    exact ⟨hcells, hheads⟩
  exact ⟨base, hdimBase, hdimBaseHead, hcoordBase, hcoordBaseHead, hwork⟩


end BitDFT.ReaderHostFrame
end

abbrev solution := @BitDFT.ReaderHostFrame.solution
