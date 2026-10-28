-- Prove2me | solution 1 for BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame_with_work_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:12:59.510053+00:00
-- url     : https://prove2.me/submissions/9960938d-c3a1-4426-a5ff-6427f9988b5a

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_component_tape
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_extra_tape
import Theorems.Thm_BitDFT_header_inverse_fourier_bank
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace BitDFT.CPLocal
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) := BankedTripleAlphabetHost.multiplierMachine A (tracked M) H

def multiplierTapeRoute (A M H : MultitapeTM) (i : Fin (tracked M).k) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) := by
  let X := tracked M
  have hX : X.k ≤ DedicatedTapeBanks.width A X H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k
    have hX := X.two_le_k
    have hH := H.two_le_k
    omega
  let r := DedicatedTapeBanks.width A X H - X.k
  let h : X.k + r = DedicatedTapeBanks.width A X H := Nat.add_sub_of_le hX
  exact BankedTripleAlphabetHost.route A X H
    (DedicatedTapeBanks.multiplierOffset A X H)
    (by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.multiplierOffset, DedicatedTapeBanks.tail]
      omega)
    (Fin.cast h (TapeExtension.oldTape X r i))

def fourierRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.fourierOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.fourierOffset, DedicatedTapeBanks.tail]; omega)

def headerRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.headerOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega)

def parkedCells (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ →
      (BankedTripleAlphabetHost.carrier A (tracked M) H).Sym := by
  let R := fourierRoute A M H
  exact fun p x =>
    let j := R.symm p
    if hj : j.val < A.k then
      (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells ⟨j.val, hj⟩ x)
    else if x = 0 then (BankedTripleAlphabetHost.carrier A (tracked M) H).startSym
      else (BankedTripleAlphabetHost.carrier A (tracked M) H).blank

def parkedHeads (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ := by
  let R := fourierRoute A M H
  exact fun p =>
    let j := R.symm p
    if hj : j.val < A.k then cF.head ⟨j.val, hj⟩ else 1

theorem hostAlphabet_tape_embed {X Y : MultitapeTM}
    (e : AlphabetEmbedding.Map X Y) (w : List X.Sym) :
    (fun p => e.encode (X.tapeOf w p)) = Y.tapeOf (w.map e.encode) := by
  funext p
  cases p with
  | zero => exact e.marker
  | succ p =>
      simp [MultitapeTM.tapeOf]
      cases h : w[p]? <;> simp [h, e.blank]
theorem header_frame_keeps_fourier_tape (A M H : MultitapeTM)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (p : Fin (DedicatedTapeBanks.width A (tracked M) H))
    (hp : p.val = j.val) :
    let eH := TripleAlphabet.header A (tracked M) H
    let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
    let hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega
    let hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
      rw [DedicatedTapeBanks.width_eq_sum]
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      omega
    let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
      (parkedCells A M H cF) (parkedHeads A M H cF) cH
    cfg.cells p =
      (fun x => (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells j x)) ∧
    cfg.head p = cF.head j := by
  let eH := TripleAlphabet.header A (tracked M) H
  let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
  have hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
    dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  have hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH
  let Rh := headerRoute A M H
  let Rf := fourierRoute A M H
  have hpA : j.val < A.k := j.isLt
  have hRF : Rf ⟨j.val, by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.width, DedicatedTapeBanks.tail]; omega⟩ = p := by
    apply Fin.ext
    have haddr := DedicatedTapeBanks.fourier_work_address A (tracked M) H j hj
    have hv := congrArg Fin.val haddr
    simpa [Rf, fourierRoute, BankedTripleAlphabetHost.route,
      DedicatedTapeBanks.fourierOffset] using hv.trans hp.symm
  have hjinv : Rf.symm p = ⟨j.val, by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.width, DedicatedTapeBanks.tail]; omega⟩ := by
    calc
      Rf.symm p = Rf.symm (Rf ⟨j.val, by
        have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.width, DedicatedTapeBanks.tail]; omega⟩) := by rw [hRF]
      _ = _ := Rf.symm_apply_apply _
  have hheaderInv : H.k ≤ (Rh.symm p).val := by
    apply BitDFT.header_inverse_fourier_bank A (tracked M) H p
    · have hppos : 1 ≤ p.val := by omega
      exact hppos
    · have hplt : p.val < A.k := by omega
      exact hplt
  have hExtra := BankedTripleAlphabetHost.config_extra_tape A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH (Rh.symm p) hheaderInv
  have hrouteBack : Rh ((Rh.symm p)) = p := Rh.apply_symm_apply p
  have hExtra' : cfg.cells (Rh (Rh.symm p)) = parkedCells A M H cF (Rh (Rh.symm p)) ∧
      cfg.head (Rh (Rh.symm p)) = parkedHeads A M H cF (Rh (Rh.symm p)) := by
    simpa [cfg, Rh, headerRoute, hoff] using hExtra
  rw [hrouteBack] at hExtra'
  change cfg.cells p = (fun x => (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells j x)) ∧
    cfg.head p = cF.head j
  constructor
  · simpa [parkedCells, Rf, hjinv, hpA] using hExtra'.1
  · simpa [parkedHeads, Rf, hjinv, hpA] using hExtra'.2


/-- The parsed dimension stays at the host address reserved for the staging
    controller, with the header embedding applied symbol by symbol. -/
theorem header_frame_dimension_projection (A M H : MultitapeTM)
    (hH4 : 3 < H.k) (cF : A.Cfg) (cH : H.Cfg) :
    let eH := TripleAlphabet.header A (tracked M) H
    let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
    let hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega
    let hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
      rw [DedicatedTapeBanks.width_eq_sum]
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      omega
    let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
      (parkedCells A M H cF) (parkedHeads A M H cF) cH
    cfg.cells (BankedOperandStage.dimensionTape A M H) =
      (fun p => eH.encode (cH.cells ⟨3, by
        have hH := hH4
        exact by omega⟩ p)) ∧
    cfg.head (BankedOperandStage.dimensionTape A M H) = cH.head ⟨3, by
      have hH := hH4
      exact by omega⟩ := by
  let eH := TripleAlphabet.header A (tracked M) H
  let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
  have hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
    dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  have hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH
  let r := DedicatedTapeBanks.width A (tracked M) H - H.k
  let h : H.k + r = DedicatedTapeBanks.width A (tracked M) H := Nat.add_sub_of_le hX
  let j : Fin H.k := ⟨3, by exact hH4⟩
  let logical := Fin.cast h (TapeExtension.oldTape H r j)
  have hcomp := BankedTripleAlphabetHost.config_component_tape A (tracked M) H H eH
    hoff hhoff hX (parkedCells A M H cF) (parkedHeads A M H cF) cH j
  have haddr : headerRoute A M H logical = BankedOperandStage.dimensionTape A M H := by
    apply Fin.ext
    have hv := congrArg Fin.val (DedicatedTapeBanks.header_value_tape_address A (tracked M) H)
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    simp [headerRoute, hoff, logical, j, TapeExtension.oldTape, Fin.cast, BankedTripleAlphabetHost.route,
      DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail,
      BankedOperandStage.dimensionTape] at hv ⊢
    omega
  have hcomp' := hcomp
  change cfg.cells (headerRoute A M H logical) =
      (fun p => eH.encode (cH.cells j p)) ∧
    cfg.head (headerRoute A M H logical) = cH.head j at hcomp'
  rw [haddr] at hcomp'
  simpa [cfg, j] using hcomp'


theorem encode_tapeOf_bits {X Y : MultitapeTM}
    (e : BitDFT.AlphabetEmbedding.Map X Y) (w : List Bool) :
    (fun p => e.encode (X.tapeOf (w.map X.bitSym) p)) =
      Y.tapeOf (w.map Y.bitSym) := by
  have hbits : (w.map X.bitSym).map e.encode = w.map Y.bitSym := by
    induction w with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons]
      rw [ih]
      cases b <;> simp [MultitapeTM.bitSym, e.zero, e.one]
  rw [hostAlphabet_tape_embed e (w.map X.bitSym)]
  rw [hbits]

theorem cp_main_aux (A M H : MultitapeTM)
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

end BitDFT.CPLocal

open BitDFT BitDFT.CPLocal IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost in
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
        base.head (multiplierTapeRoute A M H i) = 1 :=
  BitDFT.CPLocal.cp_main_aux A M H hH4 cF cH j hj dimension low sign high hcoord hdim hdimHead

end
