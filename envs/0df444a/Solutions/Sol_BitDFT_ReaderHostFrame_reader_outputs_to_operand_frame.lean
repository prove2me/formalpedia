-- Prove2me | solution 1 for BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T16:16:49.268904+00:00
-- url     : https://prove2.me/submissions/67fb163b-9a47-4a0e-9db1-dffd3335fcd2

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_component_tape
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_extra_tape
import Theorems.Thm_BitDFT_header_inverse_fourier_bank
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) := BankedTripleAlphabetHost.multiplierMachine A (tracked M) H

private def fourierRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.fourierOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.fourierOffset, DedicatedTapeBanks.tail]; omega)

private def headerRoute (A M H : MultitapeTM) :=
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
    else (BankedTripleAlphabetHost.carrier A (tracked M) H).blank

def parkedHeads (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ := by
  let R := fourierRoute A M H
  exact fun p =>
    let j := R.symm p
    if hj : j.val < A.k then cF.head ⟨j.val, hj⟩ else 1

/-- Embedding the header machine in its bank leaves every Fourier-bank tape
    at the routed location with its encoded cells and original head. -/
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


private theorem local_tape_embed {X Y : MultitapeTM}
    (e : BitDFT.AlphabetEmbedding.Map X Y) (w : List X.Sym) :
    (fun p => e.encode (X.tapeOf w p)) =
      (BitDFT.AlphabetEmbedding.machine e).tapeOf (w.map e.encode) := by
  funext p
  cases p with
  | zero => exact e.marker
  | succ p =>
    simp only [MultitapeTM.tapeOf, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : w[p]? <;> simp [h, e.blank]

private theorem encode_tapeOf_bits {X Y : MultitapeTM}
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
  rw [local_tape_embed e (w.map X.bitSym)]
  rw [hbits]
  funext p
  cases p <;> rfl


/-- Combine exact Fourier-coordinate and parsed-dimension component frames in
    the tracked-multiplier host. The coordinate head is set to the staging
    theorem's convenient terminator position; the entry frame irrelevance
    lemma lets the actual reader head be used when the run is composed. -/
theorem reader_outputs_to_operand_frame_proof (A M H : MultitapeTM)
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
        (host A M H).tapeOf (([sign, high] ++ low).map
          (host A M H).bitSym) ∧
      base.head (BankedOperandStage.coordinateTape A M H j) = low.length + 3 := by
  let N := host A M H
  let eF := TripleAlphabet.fourier A (tracked M) H
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
  let coord := BankedOperandStage.coordinateTape A M H j
  let dim := BankedOperandStage.dimensionTape A M H
  let base : (BankedOperandStage.controller A M H j hj).machine.Cfg :=
    ⟨OperandStage.State.skipSign, cfg.cells,
      fun i => if i.val = coord.val then low.length + 3 else cfg.head i⟩
  have hcoordinate := header_frame_keeps_fourier_tape A M H cF cH j hj coord (by
    rfl)
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
    have hpeq : coord.val = j.val := by rfl
    have hraw' : cfg.cells coord = (fun x => eF.encode (cF.cells j x)) := by
      simpa [coord] using hraw
    rw [hcoord] at hraw'
    have hT := hraw'.trans (encode_tapeOf_bits eF ([sign, high] ++ low))
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
  have hdimBase : base.cells dim = N.tapeOf (dimension.map N.bitSym) := by
    exact hdimEnc
  have hcoordBase : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) := by
    exact hcoordEnc
  have hdimBaseHead : base.head dim = dimension.length + 1 := by
    have hne : coord ≠ dim := by
      exact BankedOperandStage.coordinate_ne_dimension A M H j
    have hneVal : coord.val ≠ dim.val := by
      intro hv
      apply hne
      exact Fin.ext hv
    change (if dim.val = coord.val then low.length + 3 else cfg.head dim) = _
    have hn : dim.val ≠ coord.val := fun h => hneVal h.symm
    rw [if_neg hn]
    exact hdimHeadCfg
  have hcoordBaseHead : base.head coord = low.length + 3 := by
    change (if coord.val = coord.val then low.length + 3 else cfg.head coord) = _
    simp
  exact ⟨base, hdimBase, hdimBaseHead, hcoordBase, hcoordBaseHead⟩

end BitDFT.ReaderHostFrame
end

abbrev solution := BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame_proof
