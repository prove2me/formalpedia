-- Prove2me | solution 1 for DistVerif.Simulation.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T16:37:40.373708+00:00
-- url     : https://prove2.me/submissions/35d55c1f-4a1b-4e06-a1b1-da2c27204640

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network
import Definitions.Def_DistVerif_Simulation_Algorithm
import Definitions.Def_DistVerif_Simulation_Protocol
import Theorems.Thm_DistVerif_Simulation_lemma_3_4

open DistVerif.Simulation

/-! Proof of `DistVerif.Simulation.theorem_3_1` (the Simulation Theorem of Das Sarma et al.),
as a reduction to the proved `lemma_3_4`.

Plan. For each fixed random string `ω`, Alice and Bob run a deterministic protocol that keeps,
round by round, the states of `L_t` (Alice) and `R_t` (Bob). The transcript is cut into rounds
of `2N` bits, `N = d·p·B`: in round `t + 1` Alice first sends the `d·p` slot messages of
Lemma 3.4 that Bob needs (`N` bits), then Bob sends the `d·p` messages Alice needs. A party has
no memory in `DetProtocol`, so each time it speaks it rebuilds its states from its own input and
the transcript (`stA`, `stB`). After `T` rounds `s ∈ L_T` and `r ∈ R_T`, so the outputs are those
of the network algorithm; the shared random string is reused, so the error events coincide. -/

namespace SimThmAux

/-- The execution `σ_A(·, t, x, y)` on `G(Γ, d, p)`. -/
abbrev Ex (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (x y : Fin b → Bool) (t : ℕ) : Vtx Γ d p → A.State :=
  A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y t

/-- The messages on the slot edges `e`, computed from a (total) state function `c`. -/
def msgFrom {V S : Type} {B : ℕ} (send : V → V → S → Msg B) {n : ℕ}
    (e : Fin n → Option (V × V)) (c : V → S) : Fin n → Msg B :=
  fun i => match e i with
    | some (w, u) => send w u (c w)
    | none => fun _ => false

/-- Lemma 3.4's data for one round, with the update rules extended to total state functions. -/
structure RoundData (V S : Type) (n B : ℕ) where
  eL : Fin n → Option (V × V)
  gL : (V → S) → (Fin n → Msg B) → (V → S)
  eR : Fin n → Option (V × V)
  gR : (V → S) → (Fin n → Msg B) → (V → S)

/-- What round `t`'s data must do: each update rule is correct on its region given correct old
states and the true slot messages, and the slot messages only read states inside the other
party's old region. -/
def Good (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b) (t : ℕ)
    (D : RoundData (Vtx Γ d p) A.State (d * p) B) : Prop :=
  (∀ (x y : Fin b → Bool) (cA : Vtx Γ d p → A.State) (m : Fin (d * p) → Msg B),
      (∀ v ∈ L Γ d p (t - 1), cA v = Ex Γ d p B b hdp A x y (t - 1) v) →
      m = msgFrom A.send D.eL (Ex Γ d p B b hdp A x y (t - 1)) →
      ∀ v ∈ L Γ d p t, D.gL cA m v = Ex Γ d p B b hdp A x y t v) ∧
  (∀ (x y : Fin b → Bool) (cB : Vtx Γ d p → A.State),
      (∀ v ∈ R Γ d p (t - 1), cB v = Ex Γ d p B b hdp A x y (t - 1) v) →
      msgFrom A.send D.eL cB = msgFrom A.send D.eL (Ex Γ d p B b hdp A x y (t - 1))) ∧
  (∀ (x y : Fin b → Bool) (cB : Vtx Γ d p → A.State) (m : Fin (d * p) → Msg B),
      (∀ v ∈ R Γ d p (t - 1), cB v = Ex Γ d p B b hdp A x y (t - 1) v) →
      m = msgFrom A.send D.eR (Ex Γ d p B b hdp A x y (t - 1)) →
      ∀ v ∈ R Γ d p t, D.gR cB m v = Ex Γ d p B b hdp A x y t v) ∧
  (∀ (x y : Fin b → Bool) (cA : Vtx Γ d p → A.State),
      (∀ v ∈ L Γ d p (t - 1), cA v = Ex Γ d p B b hdp A x y (t - 1) v) →
      msgFrom A.send D.eR cA = msgFrom A.send D.eR (Ex Γ d p B b hdp A x y (t - 1)))

/-- Lemma 3.4 provides good round data. -/
theorem good_exists (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b) (t : ℕ)
    (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    ∃ D, Good Γ d p B b hdp A t D := by
  obtain ⟨⟨eL, gL, hL1, hL2⟩, ⟨eR, gR, hR1, hR2⟩⟩ :=
    DistVerif.Simulation.lemma_3_4 Γ d p B b hdp A t ht0 ht
  refine ⟨⟨eL, fun c m v => if hv : v ∈ L Γ d p t then gL (fun u => c u.1) m ⟨v, hv⟩
      else A.initO v, eR, fun c m v => if hv : v ∈ R Γ d p t then gR (fun u => c u.1) m ⟨v, hv⟩
      else A.initO v⟩, ?_, ?_, ?_, ?_⟩
  · intro x y cA m hcA hm v hv
    simp only [dif_pos hv]
    have hc : (fun u : ↥(L Γ d p (t - 1)) => cA u.1) =
        fun u => Ex Γ d p B b hdp A x y (t - 1) u.1 := funext fun u => hcA u.1 u.2
    rw [hc, hm]
    convert (congrFun (hL2 x y) ⟨v, hv⟩).symm using 2
    funext i
    simp only [msgFrom]
    rcases eL i with _ | ⟨w, u⟩ <;> rfl
  · intro x y cB hcB
    funext i
    simp only [msgFrom]
    rcases h : eL i with _ | ⟨w, u⟩
    · rfl
    · simp only [hcB w (hL1 i w u h).1]
  · intro x y cB m hcB hm v hv
    simp only [dif_pos hv]
    have hc : (fun u : ↥(R Γ d p (t - 1)) => cB u.1) =
        fun u => Ex Γ d p B b hdp A x y (t - 1) u.1 := funext fun u => hcB u.1 u.2
    rw [hc, hm]
    convert (congrFun (hR2 x y) ⟨v, hv⟩).symm using 2
    funext i
    simp only [msgFrom]
    rcases eR i with _ | ⟨w, u⟩ <;> rfl
  · intro x y cA hcA
    funext i
    simp only [msgFrom]
    rcases h : eR i with _ | ⟨w, u⟩
    · rfl
    · simp only [hcA w (hR1 i w u h).1]

theorem exists_round (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b) (t : ℕ) :
    ∃ D : RoundData (Vtx Γ d p) A.State (d * p) B,
      0 < t → (t : ℝ) < ((d : ℝ) ^ p - 1) / 2 → Good Γ d p B b hdp A t D := by
  by_cases h : 0 < t ∧ (t : ℝ) < ((d : ℝ) ^ p - 1) / 2
  · obtain ⟨D, hD⟩ := good_exists Γ d p B b hdp A t h.1 h.2
    exact ⟨D, fun _ _ => hD⟩
  · exact ⟨⟨fun _ => none, fun c _ => c, fun _ => none, fun c _ => c⟩,
      fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

/-- The round data used in round `t` (chosen once, independent of the inputs). -/
noncomputable def roundD (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (t : ℕ) : RoundData (Vtx Γ d p) A.State (d * p) B :=
  Classical.choose (exists_round Γ d p B b hdp A t)

theorem roundD_spec (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b) (t : ℕ)
    (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    Good Γ d p B b hdp A t (roundD Γ d p B b hdp A t) :=
  Classical.choose_spec (exists_round Γ d p B b hdp A t) ht0 ht

/-! ### Bit encoding -/

/-- Read `n` messages of `B` bits from the bit stream `β`, starting at position `start`. -/
def decode (n B : ℕ) (β : ℕ → Bool) (start : ℕ) : Fin n → Msg B :=
  fun i j => β (start + ((i : ℕ) * B + j))

/-- Bit number `o` of the message block `M` (message `o / B`, bit `o % B`). -/
def readMsg {n B : ℕ} (M : Fin n → Msg B) (o : ℕ) : Bool :=
  if h : o / B < n ∧ o % B < B then M ⟨o / B, h.1⟩ ⟨o % B, h.2⟩ else false

theorem readMsg_spec {n B : ℕ} (M : Fin n → Msg B) (i : Fin n) (j : Fin B) :
    readMsg M ((i : ℕ) * B + j) = M i j := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have h1 : ((i : ℕ) * B + j) / B = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt j.isLt, zero_add]
  have h2 : ((i : ℕ) * B + j) % B = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  have hc : ((i : ℕ) * B + j) / B < n ∧ ((i : ℕ) * B + j) % B < B := by
    rw [h1, h2]; exact ⟨i.isLt, j.isLt⟩
  rw [readMsg, dif_pos hc]
  have e1 : (⟨((i : ℕ) * B + j) / B, hc.1⟩ : Fin n) = i := Fin.ext h1
  have e2 : (⟨((i : ℕ) * B + j) % B, hc.2⟩ : Fin B) = j := Fin.ext h2
  rw [e1, e2]

theorem slot_lt {n B : ℕ} (i : Fin n) (j : Fin B) : (i : ℕ) * B + j < n * B := by
  have h := Nat.mul_le_mul_right B (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at h
  have := j.isLt
  omega

theorem divmod_aux (t c M : ℕ) (hc : c < M) : (t * M + c) / M = t ∧ (t * M + c) % M = c := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hc
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hc, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

def toβ (τ : List Bool) : ℕ → Bool := fun i => τ.getD i false

/-! ### The simulating protocol -/

/-- Alice's states after round `t`, rebuilt from `x` and the bit stream `β`. -/
noncomputable def stA (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (x : Fin b → Bool) (β : ℕ → Bool) : ℕ → Vtx Γ d p → A.State
  | 0 => Ex Γ d p B b hdp A x (fun _ => false) 0
  | t + 1 => (roundD Γ d p B b hdp A (t + 1)).gL (stA Γ d p B b hdp A x β t)
      (decode (d * p) B β (t * (2 * (d * p * B)) + d * p * B))

/-- Bob's states after round `t`, rebuilt from `y` and the bit stream `β`. -/
noncomputable def stB (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (y : Fin b → Bool) (β : ℕ → Bool) : ℕ → Vtx Γ d p → A.State
  | 0 => Ex Γ d p B b hdp A (fun _ => false) y 0
  | t + 1 => (roundD Γ d p B b hdp A (t + 1)).gR (stB Γ d p B b hdp A y β t)
      (decode (d * p) B β (t * (2 * (d * p * B))))

/-- The two-party protocol simulating `T` rounds of `A`. -/
noncomputable def simProt (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (T : ℕ) : DetProtocol b where
  aliceSpeaks τ := decide (τ.length % (2 * (d * p * B)) < d * p * B)
  aliceBit x τ := readMsg
    (msgFrom A.send (roundD Γ d p B b hdp A (τ.length / (2 * (d * p * B)) + 1)).eR
      (stA Γ d p B b hdp A x (toβ τ) (τ.length / (2 * (d * p * B)))))
    (τ.length % (2 * (d * p * B)))
  bobBit y τ := readMsg
    (msgFrom A.send (roundD Γ d p B b hdp A (τ.length / (2 * (d * p * B)) + 1)).eL
      (stB Γ d p B b hdp A y (toβ τ) (τ.length / (2 * (d * p * B)))))
    (τ.length % (2 * (d * p * B)) - d * p * B)
  outA x τ := A.outS (stA Γ d p B b hdp A x (toβ τ) T (sNode Γ d p hdp))
  outB y τ := A.outR (stB Γ d p B b hdp A y (toβ τ) T (rNode Γ d p hdp))

theorem simProt_aliceSpeaks (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (T : ℕ) (τ : List Bool) : (simProt Γ d p B b hdp A T).aliceSpeaks τ =
      decide (τ.length % (2 * (d * p * B)) < d * p * B) := rfl

theorem simProt_aliceBit (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (T : ℕ) (x : Fin b → Bool) (τ : List Bool) : (simProt Γ d p B b hdp A T).aliceBit x τ =
      readMsg (msgFrom A.send (roundD Γ d p B b hdp A (τ.length / (2 * (d * p * B)) + 1)).eR
        (stA Γ d p B b hdp A x (toβ τ) (τ.length / (2 * (d * p * B)))))
      (τ.length % (2 * (d * p * B))) := rfl

theorem simProt_bobBit (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (T : ℕ) (y : Fin b → Bool) (τ : List Bool) : (simProt Γ d p B b hdp A T).bobBit y τ =
      readMsg (msgFrom A.send (roundD Γ d p B b hdp A (τ.length / (2 * (d * p * B)) + 1)).eL
        (stB Γ d p B b hdp A y (toβ τ) (τ.length / (2 * (d * p * B)))))
      (τ.length % (2 * (d * p * B)) - d * p * B) := rfl

/-! ### Transcript bookkeeping -/

theorem transcript_length {b : ℕ} (P : DetProtocol b) (x y : Fin b → Bool) (m : ℕ) :
    (P.transcript x y m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [DetProtocol.transcript, ih]

/-- Earlier bits never change. -/
theorem transcript_getD {b : ℕ} (P : DetProtocol b) (x y : Fin b → Bool) (i m : ℕ)
    (h : i < m) : (P.transcript x y m).getD i false = (P.transcript x y (i + 1)).getD i false := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [← ih h']
      simp only [DetProtocol.transcript]
      exact List.getD_append _ _ _ _ (by rw [transcript_length]; exact h')
    · subst h'; rfl

/-- Bit `i` is the one sent by whoever speaks after `i` bits. -/
theorem transcript_bit {b : ℕ} (P : DetProtocol b) (x y : Fin b → Bool) (i : ℕ) :
    (P.transcript x y (i + 1)).getD i false =
      if P.aliceSpeaks (P.transcript x y i) then P.aliceBit x (P.transcript x y i)
      else P.bobBit y (P.transcript x y i) := by
  simp only [DetProtocol.transcript]
  rw [List.getD_append_right _ _ _ _ (by rw [transcript_length]), transcript_length]
  simp

/-! ### Regions at the start and the end -/

theorem L0_ne_r (Γ d p : ℕ) (hdp : 0 < d ^ p) (v : Vtx Γ d p) (hv : v ∈ L Γ d p 0) :
    v ≠ rNode Γ d p hdp := by
  rintro rfl
  simp [L, InLeft, rNode] at hv

theorem R0_ne_s (Γ d p : ℕ) (hdp : 0 < d ^ p) (v : Vtx Γ d p) (hv : v ∈ R Γ d p 0) :
    v ≠ sNode Γ d p hdp := by
  rintro rfl
  simp [R, InRight, sNode] at hv

theorem s_mem_L (Γ d p T : ℕ) (hdp : 0 < d ^ p) (hN : 2 * T + 1 < d ^ p) :
    sNode Γ d p hdp ∈ L Γ d p T := by
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, sNode, InLeft]
  split_ifs with h0
  · simp only [Fin.val_last, true_and]
    omega
  · exact ⟨⟨0, hdp⟩, by simp only; omega, by simp⟩

theorem r_mem_R (Γ d p T : ℕ) (hdp : 0 < d ^ p) (hN : 2 * T + 1 < d ^ p) :
    rNode Γ d p hdp ∈ R Γ d p T := by
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, rNode, InRight]
  split_ifs with h0
  · simp only [Fin.val_last, true_and]
    omega
  · refine ⟨⟨d ^ p - 1, by omega⟩, by simp only; omega, ?_⟩
    simp [Fin.val_last]

/-! ### Correctness of the simulation -/

/-- Main invariant: once the transcript covers round `t`, Alice's rebuilt states are correct on
`L_t` and Bob's on `R_t`. -/
theorem sim_invariant (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b) (T : ℕ)
    (hT : (T : ℝ) < ((d : ℝ) ^ p - 1) / 2) (x y : Fin b → Bool) :
    ∀ t, t ≤ T → ∀ m, t * (2 * (d * p * B)) ≤ m →
      (∀ v ∈ L Γ d p t, stA Γ d p B b hdp A x
          (toβ ((simProt Γ d p B b hdp A T).transcript x y m)) t v =
        Ex Γ d p B b hdp A x y t v) ∧
      (∀ v ∈ R Γ d p t, stB Γ d p B b hdp A y
          (toβ ((simProt Γ d p B b hdp A T).transcript x y m)) t v =
        Ex Γ d p B b hdp A x y t v) := by
  intro t
  induction t with
  | zero =>
    intro _ m _
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hvr := L0_ne_r Γ d p hdp v hv
      simp only [stA, Ex, DetAlg.exec]
      split_ifs <;> first | rfl | contradiction
    · have hvs := R0_ne_s Γ d p hdp v hv
      simp only [stB, Ex, DetAlg.exec]
      split_ifs <;> first | rfl | contradiction
  | succ t ih =>
    intro htT m hm
    have hreal : ((t + 1 : ℕ) : ℝ) < ((d : ℝ) ^ p - 1) / 2 :=
      lt_of_le_of_lt (by exact_mod_cast htT) hT
    obtain ⟨hG1, hG2, hG3, hG4⟩ := roundD_spec Γ d p B b hdp A (t + 1) (Nat.succ_pos t) hreal
    simp only [Nat.add_sub_cancel] at hG1 hG2 hG3 hG4
    have hm' : t * (2 * (d * p * B)) + 2 * (d * p * B) ≤ m := by
      rw [Nat.succ_mul] at hm; exact hm
    obtain ⟨ihA, ihB⟩ := ih (by omega) m (by omega)
    -- Bob's half of round `t + 1`: the bits Alice decodes are the true `eL` messages.
    have hbob : decode (d * p) B (toβ ((simProt Γ d p B b hdp A T).transcript x y m))
        (t * (2 * (d * p * B)) + d * p * B) =
        msgFrom A.send (roundD Γ d p B b hdp A (t + 1)).eL (Ex Γ d p B b hdp A x y t) := by
      funext i j
      have hs := slot_lt i j
      obtain ⟨hdiv, hmod⟩ := divmod_aux t (d * p * B + ((i : ℕ) * B + j)) (2 * (d * p * B))
        (by omega)
      have hpm : t * (2 * (d * p * B)) + (d * p * B + ((i : ℕ) * B + j)) < m := by omega
      have hlen := transcript_length (simProt Γ d p B b hdp A T) x y
        (t * (2 * (d * p * B)) + (d * p * B + ((i : ℕ) * B + j)))
      simp only [decode, toβ]
      rw [Nat.add_assoc, transcript_getD _ _ _ _ _ hpm, transcript_bit, simProt_aliceSpeaks,
        hlen, hmod, if_neg (by simp), simProt_bobBit, hlen, hdiv, hmod, Nat.add_sub_cancel_left,
        readMsg_spec]
      obtain ⟨-, ihBp⟩ := ih (by omega)
        (t * (2 * (d * p * B)) + (d * p * B + ((i : ℕ) * B + j))) (by omega)
      exact congrFun (congrFun (hG2 x y _ ihBp) i) j
    -- Alice's half of round `t + 1`: the bits Bob decodes are the true `eR` messages.
    have halice : decode (d * p) B (toβ ((simProt Γ d p B b hdp A T).transcript x y m))
        (t * (2 * (d * p * B))) =
        msgFrom A.send (roundD Γ d p B b hdp A (t + 1)).eR (Ex Γ d p B b hdp A x y t) := by
      funext i j
      have hs := slot_lt i j
      obtain ⟨hdiv, hmod⟩ := divmod_aux t ((i : ℕ) * B + j) (2 * (d * p * B)) (by omega)
      have hpm : t * (2 * (d * p * B)) + ((i : ℕ) * B + j) < m := by omega
      have hlen := transcript_length (simProt Γ d p B b hdp A T) x y
        (t * (2 * (d * p * B)) + ((i : ℕ) * B + j))
      simp only [decode, toβ]
      rw [transcript_getD _ _ _ _ _ hpm, transcript_bit, simProt_aliceSpeaks, hlen, hmod,
        if_pos (by simp; omega), simProt_aliceBit, hlen, hdiv, hmod, readMsg_spec]
      obtain ⟨ihAp, -⟩ := ih (by omega)
        (t * (2 * (d * p * B)) + ((i : ℕ) * B + j)) (by omega)
      exact congrFun (congrFun (hG4 x y _ ihAp) i) j
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [stA]
      exact hG1 x y _ _ ihA hbob v hv
    · rw [stB]
      exact hG3 x y _ _ ihB halice v hv

/-- For each fixed deterministic algorithm, the protocol's outputs are the network's outputs. -/
theorem sim_correct (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b) (T : ℕ)
    (hT : (T : ℝ) < ((d : ℝ) ^ p - 1) / 2) (x y : Fin b → Bool) :
    (simProt Γ d p B b hdp A T).outA x
        ((simProt Γ d p B b hdp A T).transcript x y (T * (2 * (d * p * B)))) =
      A.outS (Ex Γ d p B b hdp A x y T (sNode Γ d p hdp)) ∧
    (simProt Γ d p B b hdp A T).outB y
        ((simProt Γ d p B b hdp A T).transcript x y (T * (2 * (d * p * B)))) =
      A.outR (Ex Γ d p B b hdp A x y T (rNode Γ d p hdp)) := by
  have hN : 2 * T + 1 < d ^ p := by
    have h1 : ((2 * T + 1 : ℕ) : ℝ) < ((d ^ p : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  obtain ⟨hA, hB⟩ := sim_invariant Γ d p B b hdp A T hT x y T le_rfl _ le_rfl
  exact ⟨congrArg A.outS (hA _ (s_mem_L Γ d p T hdp hN)),
    congrArg A.outR (hB _ (r_mem_R Γ d p T hdp hN))⟩

end SimThmAux

theorem solution (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (Fin b → Bool) → (Fin b → Bool) → Bool) (T : ℕ)
    (hT : (T : ℝ) < ((d : ℝ) ^ p - 1) / 2) (A : PubAlg (Vtx Γ d p) B b)
    (hA : A.ComputesWithin (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) T f ε) :
    ∃ k : ℕ, k ≤ 2 * d * p * B * T ∧ ∃ P : PubProtocol b, P.ComputesWithin k f ε := by
  -- Same shared randomness; for each `ω` run the deterministic simulation of `A.alg ω`.
  refine ⟨T * (2 * (d * p * B)), le_of_eq (by ring),
    ⟨A.Ω, A.μ, fun ω => SimThmAux.simProt Γ d p B b hdp (A.alg ω) T⟩, ?_⟩
  intro x y
  have hset : {ω | ¬ ((SimThmAux.simProt Γ d p B b hdp (A.alg ω) T).outA x
        ((SimThmAux.simProt Γ d p B b hdp (A.alg ω) T).transcript x y (T * (2 * (d * p * B))))
          = f x y ∧
      (SimThmAux.simProt Γ d p B b hdp (A.alg ω) T).outB y
        ((SimThmAux.simProt Γ d p B b hdp (A.alg ω) T).transcript x y (T * (2 * (d * p * B))))
          = f x y)} =
      {ω | ¬ ((A.alg ω).outS ((A.alg ω).exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp)
          x y T (sNode Γ d p hdp)) = f x y ∧
        (A.alg ω).outR ((A.alg ω).exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp)
          x y T (rNode Γ d p hdp)) = f x y)} := by
    ext ω
    obtain ⟨h1, h2⟩ := SimThmAux.sim_correct Γ d p B b hdp (A.alg ω) T hT x y
    simp only [Set.mem_setOf_eq, h1, h2]
  show A.μ.toOuterMeasure _ ≤ _
  rw [hset]
  exact hA x y
