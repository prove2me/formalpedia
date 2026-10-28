-- Prove2me | solution 1 for BitDFT.BankedTripleAlphabetHost.config_extra_tape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:30:04.783688+00:00
-- url     : https://prove2.me/submissions/6f5446c1-bc25-40af-a7e1-44150ef72444

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Theorems.Thm_BitDFT_tape_permutation_run

set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedTripleAlphabetHost
open IntMul BitDFT.AlphabetEmbedding

/-- Exact-clock execution of a component in its disjoint work-tape bank;
    all other physical tapes retain their caller contents. -/
theorem run (A M H X : MultitapeTM) (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ) (c : X.Cfg) (t : ℕ) :
    (machine A M H X e offset hoff hX).step^[t]
      (config A M H X e offset hoff hX extraCells extraHeads c) =
    config A M H X e offset hoff hX extraCells extraHeads (X.step^[t] c) := by
  let r := BitDFT.DedicatedTapeBanks.width A M H - X.k
  let h : X.k + r = BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
  let E0 := AlphabetEmbedding.machine e
  let P := TapeExtension.machine E0 r
  let E := TapeCountTransport.machine P (BitDFT.DedicatedTapeBanks.width A M H) h
  let R := route A M H offset hoff
  let he : R ⟨0, by have ht := BitDFT.DedicatedTapeBanks.tail_ge_two A M H; omega⟩ =
      ⟨0, by have ht := BitDFT.DedicatedTapeBanks.tail_ge_two A M H; omega⟩ :=
    BitDFT.DedicatedTapeBanks.routing_input (BitDFT.DedicatedTapeBanks.tail A M H)
      offset hoff
  let extras : Fin (E0.k + r) → ℕ → E0.Sym :=
    fun i => extraCells (R (Fin.cast h i))
  let extraHeads' : Fin (E0.k + r) → ℕ :=
    fun i => extraHeads (R (Fin.cast h i))
  let c0 := AlphabetEmbedding.embed e c
  let c1 := TapeExtension.embed E0 r extras extraHeads' c0
  have hAlpha := (BitDFT.alphabet_embedding_correct X (carrier A M H) e).1 c t
  have hExt := (BitDFT.tape_extension_correct E0 r).1 extras extraHeads' c0 t
  have hCount := BitDFT.tape_count_transport_correct P
    (BitDFT.DedicatedTapeBanks.width A M H) h c1 t
  have hPerm := BitDFT.tape_permutation_run E R he
    (TapeCountTransport.embed P (BitDFT.DedicatedTapeBanks.width A M H) h c1) t
  rw [hCount, hExt, hAlpha] at hPerm
  simpa [machine, config, route, r, h, E0, P, E, R, he, extras, extraHeads', c0, c1] using hPerm

/-- A component tape remains at the address selected by the bank routing.
    The returned symbol is embedded into the host alphabet; the head position
    is unchanged. This is the projection equation needed to compare a staged
    host buffer with the component's tracked-call frame. -/
theorem config_component_tape (A M H X : MultitapeTM)
    (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ)
    (c : X.Cfg) (j : Fin X.k) :
    let h : X.k + (BitDFT.DedicatedTapeBanks.width A M H - X.k) =
        BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
    let logical := Fin.cast h (TapeExtension.oldTape X
      (BitDFT.DedicatedTapeBanks.width A M H - X.k) j)
    (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (route A M H offset hoff logical) = (fun p => e.encode (c.cells j p)) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (route A M H offset hoff logical) = c.head j := by
  let r := BitDFT.DedicatedTapeBanks.width A M H - X.k
  let h : X.k + r = BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
  let logical := Fin.cast h (TapeExtension.oldTape X r j)
  let E0 := AlphabetEmbedding.machine e
  let P := TapeExtension.machine E0 r
  let E := TapeCountTransport.machine P (BitDFT.DedicatedTapeBanks.width A M H) h
  let R := route A M H offset hoff
  change (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (R logical) = (fun p => e.encode (c.cells j p)) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (R logical) = c.head j
  constructor <;>
    simp [config, machine, route, r, h, logical, E0, P, E, R,
      TapePermutation.embed, TapeCountTransport.embed, TapeExtension.embed,
      TapeExtension.oldTape, AlphabetEmbedding.embed]

/-- A tape routed from the appended bank keeps its caller-supplied contents
    and head exactly. In particular, Fourier and header reader results survive
    while a different component executes in its own bank. -/
theorem config_extra_tape (A M H X : MultitapeTM)
    (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ)
    (c : X.Cfg) (j : Fin (BitDFT.DedicatedTapeBanks.width A M H))
    (hj : X.k ≤ j.val) :
    (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (route A M H offset hoff j) = extraCells (route A M H offset hoff j) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (route A M H offset hoff j) = extraHeads (route A M H offset hoff j) := by
  let r := BitDFT.DedicatedTapeBanks.width A M H - X.k
  let h : X.k + r = BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
  let E0 := AlphabetEmbedding.machine e
  let P := TapeExtension.machine E0 r
  let E := TapeCountTransport.machine P (BitDFT.DedicatedTapeBanks.width A M H) h
  let R := route A M H offset hoff
  change (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (R j) = extraCells (R j) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (R j) = extraHeads (R j)
  constructor <;>
    simp [config, machine, route, r, h, E0, P, E, R, TapePermutation.embed,
      TapeCountTransport.embed, TapeExtension.embed, AlphabetEmbedding.embed,
      Nat.not_lt_of_ge hj]

/-- Any non-input physical tape outside the multiplier's routed bank is an
    appended-bank tape when viewed through the multiplier route. -/
theorem route_inverse_extra (A X H : MultitapeTM)
    (hoff : BitDFT.DedicatedTapeBanks.multiplierOffset A X H <
      4 + BitDFT.DedicatedTapeBanks.tail A X H)
    (p : Fin (BitDFT.DedicatedTapeBanks.width A X H))
    (hp : 1 ≤ p.val)
    (houtside : p.val < A.k ∨ A.k + X.k - 2 < p.val) :
    X.k ≤ ((route A X H
      (BitDFT.DedicatedTapeBanks.multiplierOffset A X H) hoff).symm p).val := by
  let offset := BitDFT.DedicatedTapeBanks.multiplierOffset A X H
  let R := route A X H offset hoff
  by_contra hnot
  have hi : (R.symm p).val < X.k := Nat.lt_of_not_ge hnot
  let i := R.symm p
  have hroute : R i = p := Equiv.apply_symm_apply R p
  by_cases hiz : i.val = 0
  · have hzero : i = ⟨0, by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [BitDFT.DedicatedTapeBanks.width,
        BitDFT.DedicatedTapeBanks.tail]
      omega⟩ := Fin.ext hiz
    rw [hzero] at hroute
    have hinput := BitDFT.DedicatedTapeBanks.routing_input
      (BitDFT.DedicatedTapeBanks.tail A X H) offset hoff
    have hv := congrArg Fin.val hroute
    rw [show R ⟨0, by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [BitDFT.DedicatedTapeBanks.width,
        BitDFT.DedicatedTapeBanks.tail]
      omega⟩ = ⟨0, by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [BitDFT.DedicatedTapeBanks.width,
        BitDFT.DedicatedTapeBanks.tail]
      omega⟩ by simpa [R, route, offset] using hinput] at hv
    have hpv := p.isLt
    omega
  · have hpos : 1 ≤ i.val := by omega
    let ii : Fin X.k := ⟨i.val, hi⟩
    have haddr := BitDFT.DedicatedTapeBanks.multiplier_work_address A X H ii hpos
    have haddrVal : (R i).val = A.k + i.val - 1 := by
      have hv := congrArg Fin.val haddr
      simpa [R, route, offset, ii] using hv
    have hv := congrArg Fin.val hroute
    rw [haddrVal] at hv
    rcases houtside with hlo | hhi <;> omega

end BitDFT.BankedTripleAlphabetHost
end


noncomputable section
open IntMul BitDFT BitDFT.AlphabetEmbedding BitDFT.BankedTripleAlphabetHost
theorem solution (A M H X : MultitapeTM)
    (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ)
    (c : X.Cfg) (j : Fin (BitDFT.DedicatedTapeBanks.width A M H))
    (hj : X.k ≤ j.val) :
    (config A M H X e offset hoff hX extraCells extraHeads c).cells
      (route A M H offset hoff j) = extraCells (route A M H offset hoff j) ∧
    (config A M H X e offset hoff hX extraCells extraHeads c).head
      (route A M H offset hoff j) = extraHeads (route A M H offset hoff j) := by
  exact BitDFT.BankedTripleAlphabetHost.config_extra_tape A M H X e offset hoff hX extraCells extraHeads c j hj
end
