-- Prove2me | solution 1 for DLSConsensus.LowerBound.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:32:32.253977+00:00
-- url     : https://prove2.me/submissions/2bede490-004c-40b9-a92a-e02aad26a1e3

import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model



namespace DLSConsensus.LowerBound

open Classical

variable {N : ℕ} {σ M : Type}

/-- result of executing an instruction -/
def stepI (ins : Instr N σ M) (S : Set (Fin N × M)) : σ :=
  match ins with
  | .send _ _ nx => nx
  | .receive f => f S

section Construct
variable (π : Protocol N σ M) (val : Fin N → Bool) (Al P : Finset (Fin N)) (T : ℕ)

def cSends (X : ℕ → Fin N → σ) (k : Fin N) (s : ℕ) (j : Fin N) (m : M) : Prop :=
  ∃ n, s = n + 1 ∧ (k ∈ Al ∧ 1 ≤ s) ∧ ∃ nx, π.instr k (X n k) = Instr.send m j nx

def cRec (X : ℕ → Fin N → σ) (j : Fin N) (s : ℕ) : Prop :=
  ∃ n, s = n + 1 ∧ (j ∈ Al ∧ 1 ≤ s) ∧ (π.instr j (X n j)).IsReceive

def okT (k j : Fin N) (n : ℕ) : Prop := (k ∈ P ↔ j ∈ P) ∨ T < n

def cDeliv (X : ℕ → Fin N → σ) (j : Fin N) (n : ℕ) : Set (Fin N × ℕ) :=
  {x | cRec π Al X j n ∧ x.2 < n ∧ (∃ m, cSends π Al X x.1 x.2 j m) ∧ okT P T x.1 j n ∧
     ∀ n', x.2 < n' → n' < n → ¬ (cRec π Al X j n' ∧ okT P T x.1 j n')}

def cDl (X : ℕ → Fin N → σ) (j : Fin N) (n : ℕ) : Set (Fin N × M) :=
  {x | ∃ s, (x.1, s) ∈ cDeliv π Al P T X j n ∧ cSends π Al X x.1 s j x.2}

def cNext (X : ℕ → Fin N → σ) (n : ℕ) (i : Fin N) : σ :=
  if i ∈ Al then stepI (π.instr i (X n i)) (cDl π Al P T X i (n + 1)) else X n i

def cTraj : ℕ → ℕ → Fin N → σ
  | 0 => fun _ i => π.init i (val i)
  | n + 1 => fun m => if m = n + 1 then (fun i => cNext π Al P T (cTraj n) n i) else cTraj n m

lemma cTraj_stable : ∀ n m, m ≤ n → cTraj π val Al P T n m = cTraj π val Al P T m m := by
  intro n
  induction n with
  | zero => intro m hm; have : m = 0 := by omega
            subst this; rfl
  | succ n ih =>
    intro m hm
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · have : cTraj π val Al P T (n + 1) m = cTraj π val Al P T n m := by
        simp [cTraj, show m ≠ n + 1 by omega]
      rw [this]; exact ih m (by omega)
    · have : m = n + 1 := by omega
      subst this; rfl

variable {π Al P T}

lemma cSends_congr {X Y : ℕ → Fin N → σ} {n : ℕ} (h : ∀ m ≤ n, X m = Y m) {k s j m'} (hs : s ≤ n + 1) :
    cSends π Al X k s j m' ↔ cSends π Al Y k s j m' := by
  unfold cSends
  constructor
  · rintro ⟨n', hn', ha, nx, hx⟩
    refine ⟨n', hn', ha, nx, ?_⟩
    rw [← h n' (by omega)]; exact hx
  · rintro ⟨n', hn', ha, nx, hx⟩
    refine ⟨n', hn', ha, nx, ?_⟩
    rw [h n' (by omega)]; exact hx

lemma cRec_congr {X Y : ℕ → Fin N → σ} {n : ℕ} (h : ∀ m ≤ n, X m = Y m) {j s} (hs : s ≤ n + 1) :
    cRec π Al X j s ↔ cRec π Al Y j s := by
  unfold cRec
  constructor
  · rintro ⟨n', hn', ha, hx⟩
    refine ⟨n', hn', ha, ?_⟩
    rw [← h n' (by omega)]; exact hx
  · rintro ⟨n', hn', ha, hx⟩
    refine ⟨n', hn', ha, ?_⟩
    rw [h n' (by omega)]; exact hx

lemma cDeliv_congr {X Y : ℕ → Fin N → σ} {n : ℕ} (h : ∀ m ≤ n, X m = Y m) {j n0} (hn0 : n0 ≤ n + 1) :
    cDeliv π Al P T X j n0 = cDeliv π Al P T Y j n0 := by
  ext ⟨k, s⟩
  simp only [cDeliv, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hr, hs, ⟨m, hm⟩, hok, hmin⟩
    refine ⟨(cRec_congr h (by omega)).1 hr, hs, ⟨m, (cSends_congr h (by omega)).1 hm⟩, hok, ?_⟩
    intro n' h1 h2 ⟨h3, h4⟩
    exact hmin n' h1 h2 ⟨(cRec_congr h (by omega)).2 h3, h4⟩
  · rintro ⟨hr, hs, ⟨m, hm⟩, hok, hmin⟩
    refine ⟨(cRec_congr h (by omega)).2 hr, hs, ⟨m, (cSends_congr h (by omega)).2 hm⟩, hok, ?_⟩
    intro n' h1 h2 ⟨h3, h4⟩
    exact hmin n' h1 h2 ⟨(cRec_congr h (by omega)).1 h3, h4⟩

lemma cDl_congr {X Y : ℕ → Fin N → σ} {n : ℕ} (h : ∀ m ≤ n, X m = Y m) {j} :
    cDl π Al P T X j (n + 1) = cDl π Al P T Y j (n + 1) := by
  ext ⟨k, m'⟩
  simp only [cDl, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hd, hs⟩
    have hd' := hd
    rw [cDeliv_congr h le_rfl] at hd'
    have hlt : s < n + 1 := by
      have := hd.2.1; simpa using this
    exact ⟨s, hd', (cSends_congr h (by omega)).1 hs⟩
  · rintro ⟨s, hd, hs⟩
    have hd' := hd
    rw [← cDeliv_congr h le_rfl] at hd'
    have hlt : s < n + 1 := by
      have := hd.2.1; simpa using this
    exact ⟨s, hd', (cSends_congr h (by omega)).2 hs⟩

lemma cNext_congr {X Y : ℕ → Fin N → σ} {n : ℕ} (h : ∀ m ≤ n, X m = Y m) (i) :
    cNext π Al P T X n i = cNext π Al P T Y n i := by
  unfold cNext
  rw [cDl_congr h, h n le_rfl]

variable (π Al P T)

/-- the constructed state function -/
def cState : ℕ → Fin N → σ := fun n => cTraj π val Al P T n n

lemma cTraj_le {n m : ℕ} (hm : m ≤ n) : cTraj π val Al P T n m = cState π val Al P T m := by
  exact cTraj_stable π val Al P T n m hm

lemma cState_succ (n : ℕ) (i : Fin N) :
    cState π val Al P T (n + 1) i = cNext π Al P T (cState π val Al P T) n i := by
  have h1 : cState π val Al P T (n + 1) = cNext π Al P T (cTraj π val Al P T n) n := by
    simp [cState, cTraj]
  rw [h1]
  exact cNext_congr (fun m hm => cTraj_le π val Al P T hm) i

/-- the constructed run -/
def cRun : Run N σ where
  val := val
  active := fun i n => i ∈ Al ∧ 1 ≤ n
  state := fun i n => cState π val Al P T n i
  deliv := fun i n => cDeliv π Al P T (cState π val Al P T) i n

lemma cRun_isRun : IsRun π (cRun π val Al P T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp [cRun, cState, cTraj]
  · intro i n hn
    have : i ∉ Al := fun h => hn ⟨h, by omega⟩
    show cState π val Al P T (n + 1) i = cState π val Al P T n i
    rw [cState_succ]; simp [cNext, this]
  · intro i n m j nx ha h
    show cState π val Al P T (n + 1) i = nx
    rw [cState_succ]
    have h' : π.instr i (cState π val Al P T n i) = Instr.send m j nx := h
    simp [cNext, ha.1, h', stepI]
  · intro i n f ha h
    show cState π val Al P T (n + 1) i = f _
    rw [cState_succ]
    have h' : π.instr i (cState π val Al P T n i) = Instr.receive f := h
    simp [cNext, ha.1, h', stepI]
    rfl
  · intro i n k s h
    obtain ⟨hr, hs, ⟨m, hm⟩, _⟩ := h
    exact ⟨hr, hs, m, hm⟩
  · intro i n n' k s h h'
    obtain ⟨hr, hs, ⟨m, hm⟩, hok, hmin⟩ := h
    obtain ⟨hr', hs', ⟨m', hm'⟩, hok', hmin'⟩ := h'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · exact hmin' n hs hl ⟨hr, hok⟩
    · exact hmin n' hs' hl ⟨hr', hok'⟩

end Construct

lemma exists_run (π : Protocol N σ M) (val : Fin N → Bool) (Al P : Finset (Fin N)) (T : ℕ) :
    ∃ R : Run N σ, IsRun π R ∧ R.val = val ∧ (∀ i n, R.active i n ↔ (i ∈ Al ∧ 1 ≤ n)) ∧
      (∀ k s j (m : M) s₂, Sends π R k s j m → s < s₂ → ReceivesAt π R j s₂ →
        ((k ∈ P ↔ j ∈ P) ∨ T < s₂) → ∃ n ≤ s₂, (k, s) ∈ R.deliv j n) ∧
      (∀ i k s n, (k, s) ∈ R.deliv i n → ¬ (k ∈ P ↔ i ∈ P) → T < n) := by
  refine ⟨cRun π val Al P T, cRun_isRun π val Al P T, rfl, fun i n => Iff.rfl, ?_, ?_⟩
  · intro k s j m s₂ hs hlt hr hok
    have hsX : cSends π Al (cState π val Al P T) k s j m := hs
    have hrX : cRec π Al (cState π val Al P T) j s₂ := hr
    have hex : ∃ n, s < n ∧ cRec π Al (cState π val Al P T) j n ∧ okT P T k j n := ⟨s₂, hlt, hrX, hok⟩
    classical
    let n0 := Nat.find hex
    have hn0 : s < n0 ∧ cRec π Al (cState π val Al P T) j n0 ∧ okT P T k j n0 := Nat.find_spec hex
    refine ⟨n0, Nat.find_min' hex ⟨hlt, hrX, hok⟩, ?_⟩
    show (k, s) ∈ cDeliv π Al P T (cState π val Al P T) j n0
    refine ⟨hn0.2.1, hn0.1, ⟨m, hsX⟩, hn0.2.2, ?_⟩
    intro n' h1 h2 ⟨h3, h4⟩
    exact Nat.find_min hex h2 ⟨h1, h3, h4⟩
  · intro i k s n hd hne
    have hd' : (k, s) ∈ cDeliv π Al P T (cState π val Al P T) i n := hd
    rcases hd'.2.2.2.1 with h | h
    · exact absurd h hne
    · exact h

lemma allowed_of_late {π : Protocol N σ M} {R : Run N σ} {cm : Comm} (hcm : cm.WF) (T : ℕ)
    (hlate : ∀ k s j (m : M) s₂, Sends π R k s j m → s < s₂ → T < s₂ → ReceivesAt π R j s₂ →
      ∃ n ≤ s₂, (k, s) ∈ R.deliv j n) : cm.Allowed π R := by
  cases cm with
  | eventually Δ =>
    exact ⟨T, fun k s j m s₂ hs hT hΔ hr => hlate k s j m s₂ hs (by simp [Comm.WF] at hcm; omega)
      (by simp [Comm.WF] at hcm; omega) hr⟩
  | unknown =>
    exact ⟨T + 1, by omega, fun k s j m s₂ hs h1 hΔ hr => hlate k s j m s₂ hs (by omega) (by omega) hr⟩

lemma allowed_of_isolated {π : Protocol N σ M} {R : Run N σ} {S : Finset (Fin N)} {v : Bool}
    {cm : Comm} (hcm : cm.WF) (h : IsolatedScenario π S v R) : cm.Allowed π R := by
  obtain ⟨hr, hval, hact, hina, hT⟩ := h
  refine allowed_of_late hcm 0 ?_
  intro k s j m s₂ hs hlt _ hrec
  have hk : k ∈ S := by
    by_contra hk
    obtain ⟨_, _, ha, _⟩ := hs
    exact hina k hk s ha
  have hj : j ∈ S := by
    by_contra hj
    obtain ⟨_, _, ha, _⟩ := hrec
    exact hina j hj s₂ ha
  exact hT k hk j hj s m s₂ hs (by omega) hrec

lemma deliv_transfer {π : Protocol N σ M} {Ra Rb : Run N σ} {S : Finset (Fin N)} {N0 : ℕ}
    (hRa : IsRun π Ra) (hRb : IsRun π Rb) (hTa : TimeOneWithin π S Ra) (hTb : TimeOneWithin π S Rb)
    (hSends : ∀ k ∈ S, ∀ s j (m : M), s ≤ N0 → (Sends π Ra k s j m ↔ Sends π Rb k s j m))
    (hRec : ∀ j ∈ S, ∀ s ≤ N0, (ReceivesAt π Ra j s ↔ ReceivesAt π Rb j s))
    {i k : Fin N} {s n' : ℕ} (hi : i ∈ S) (hk : k ∈ S) (hn' : n' ≤ N0)
    (hd : (k, s) ∈ Ra.deliv i n') : (k, s) ∈ Rb.deliv i n' := by
  obtain ⟨hrec, hs, m, hm⟩ := hRa.2.2.2.2.1 i n' k s hd
  have hrecb := (hRec i hi n' hn').1 hrec
  have hmb := (hSends k hk s i m (by omega)).1 hm
  obtain ⟨n'', hn'', hd''⟩ := hTb k hk i hi s m n' hmb (by omega) hrecb
  by_cases heq : n'' = n'
  · subst heq; exact hd''
  · exfalso
    have hlt : n'' < n' := lt_of_le_of_ne hn'' heq
    obtain ⟨hrec2, hs2, m2, hm2⟩ := hRb.2.2.2.2.1 i n'' k s hd''
    have hra2 := (hRec i hi n'' (by omega)).2 hrec2
    have hma2 := (hSends k hk s i m2 (by omega)).2 hm2
    obtain ⟨n3, hn3, hd3⟩ := hTa k hk i hi s m2 n'' hma2 (by omega) hra2
    have := hRa.2.2.2.2.2 i n3 n' k s hd3 hd
    omega

lemma compare {π : Protocol N σ M} {S : Finset (Fin N)} {T : ℕ} {R1 R2 : Run N σ} {v : Bool}
    (h1 : IsolatedScenario π S v R1) (h2 : IsRun π R2) (hv2 : ∀ i ∈ S, R2.val i = v)
    (hact2 : ∀ i ∈ S, ∀ n, 1 ≤ n → R2.active i n) (hT2 : TimeOneWithin π S R2)
    (hcross : ∀ i ∈ S, ∀ k, k ∉ S → ∀ s n, n ≤ T → (k, s) ∉ R2.deliv i n) :
    ∀ i ∈ S, ∀ n ≤ T, R2.state i n = R1.state i n := by
  obtain ⟨hr1, hval1, hact1, hina1, hT1⟩ := h1
  have key : ∀ n, n ≤ T → ∀ i ∈ S, R2.state i n = R1.state i n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn i hi
      cases n with
      | zero => rw [h2.1 i, hr1.1 i, hval1 i, hv2 i hi]
      | succ n0 =>
        have ih' : ∀ m ≤ n0, ∀ i ∈ S, R2.state i m = R1.state i m :=
          fun m hm => ih m (by omega) (by omega)
        have hSends : ∀ k ∈ S, ∀ s j (m : M), s ≤ n0 + 1 →
            (Sends π R1 k s j m ↔ Sends π R2 k s j m) := by
          intro k hk s j m hs
          constructor
          · rintro ⟨n', hn', _, nx, hx⟩
            refine ⟨n', hn', hact2 k hk s (by omega), nx, ?_⟩
            rw [ih' n' (by omega) k hk]; exact hx
          · rintro ⟨n', hn', _, nx, hx⟩
            refine ⟨n', hn', hact1 k hk s (by omega), nx, ?_⟩
            rw [← ih' n' (by omega) k hk]; exact hx
        have hRec : ∀ j ∈ S, ∀ s ≤ n0 + 1, (ReceivesAt π R1 j s ↔ ReceivesAt π R2 j s) := by
          intro j hj s hs
          constructor
          · rintro ⟨n', hn', _, hx⟩
            refine ⟨n', hn', hact2 j hj s (by omega), ?_⟩
            rw [ih' n' (by omega) j hj]; exact hx
          · rintro ⟨n', hn', _, hx⟩
            refine ⟨n', hn', hact1 j hj s (by omega), ?_⟩
            rw [← ih' n' (by omega) j hj]; exact hx
        have hdel : delivered π R1 i (n0 + 1) = delivered π R2 i (n0 + 1) := by
          ext ⟨k, m⟩
          simp only [delivered, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨s, hd, hs⟩
            have hk : k ∈ S := by
              by_contra hk
              obtain ⟨_, _, ha, _⟩ := hs
              exact hina1 k hk s ha
            have hslt := (hr1.2.2.2.2.1 i (n0 + 1) k s hd).2.1
            exact ⟨s, deliv_transfer hr1 h2 hT1 hT2 hSends hRec hi hk le_rfl hd,
              (hSends k hk s i m (by omega)).1 hs⟩
          · rintro ⟨s, hd, hs⟩
            have hk : k ∈ S := by
              by_contra hk
              exact hcross i hi k hk s (n0 + 1) hn hd
            have hslt := (h2.2.2.2.2.1 i (n0 + 1) k s hd).2.1
            exact ⟨s, deliv_transfer h2 hr1 hT2 hT1 (fun k hk s j m hs => (hSends k hk s j m hs).symm)
              (fun j hj s hs => (hRec j hj s hs).symm) hi hk le_rfl hd,
              (hSends k hk s i m (by omega)).2 hs⟩
        have ha1 := hact1 i hi (n0 + 1) (by omega)
        have ha2 := hact2 i hi (n0 + 1) (by omega)
        have hst := ih' n0 le_rfl i hi
        rcases hins : π.instr i (R1.state i n0) with ⟨m', j', nx⟩ | f
        · have hins2 : π.instr i (R2.state i n0) = Instr.send m' j' nx := by rw [hst]; exact hins
          rw [h2.2.2.1 i n0 m' j' nx ha2 hins2, hr1.2.2.1 i n0 m' j' nx ha1 hins]
        · have hins2 : π.instr i (R2.state i n0) = Instr.receive f := by rw [hst]; exact hins
          rw [h2.2.2.2.1 i n0 f ha2 hins2, hr1.2.2.2.1 i n0 f ha1 hins, hdel]
  exact fun i hi n hn => key n hn i hi

lemma decidesAt_congr {π : Protocol N σ M} {R R' : Run N σ} {i : Fin N} {v : Bool} {n : ℕ}
    (h : ∀ m ≤ n, R.state i m = R'.state i m) (hd : DecidesAt π R i v n) : DecidesAt π R' i v n := by
  refine ⟨?_, ?_⟩
  · rw [← h n le_rfl]; exact hd.1
  · intro n' hn'
    rw [← h n' hn'.le]; exact hd.2 n' hn'

lemma scen_gen (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF) (hres : Resilient π t cm)
    (P Q : Finset (Fin N)) (hdisj : Disjoint P Q) (hcover : P ∪ Q = Finset.univ)
    (hQt : Q.card ≤ t) (v : Bool) :
    (∃ R : Run N σ, IsolatedScenario π P v R) ∧
    ∀ R : Run N σ, IsolatedScenario π P v R →
      ∃ T : ℕ, ∀ i ∈ P, ∃ n ≤ T, DecidesAt π R i v n := by
  constructor
  · obtain ⟨R, hR, hv, hact, hlate, _⟩ := exists_run π (fun _ => v) P P 0
    refine ⟨R, hR, fun i => by rw [hv], fun i hi n hn => (hact i n).2 ⟨hi, hn⟩,
      fun i hi n h => hi ((hact i n).1 h).1, ?_⟩
    intro k hk j hj s m s₂ hs h1 hr
    exact hlate k s j m s₂ hs (by omega) hr (Or.inl ⟨fun _ => hj, fun _ => hk⟩)
  · intro R hiso
    have hcard : P.card + Q.card = N := by
      rw [← Finset.card_union_of_disjoint hdisj, hcover]; simp
    have hPc : N - t ≤ P.card := by omega
    obtain ⟨hRr, hval, hact, hina, hT⟩ := hiso
    have hFS : FailStop P R := ⟨fun i hi n hn => hact i hi n hn, fun i hi => ⟨0, fun n _ => hina i hi n⟩⟩
    have hAl : cm.Allowed π R := allowed_of_isolated hcm ⟨hRr, hval, hact, hina, hT⟩
    obtain ⟨_, hterm, _⟩ := hres P hPc R hRr hFS hAl
    have h : ∀ i ∈ P, ∃ w n, DecidesAt π R i w n := by
      intro i hi
      obtain ⟨w, n, hn⟩ := hterm i hi
      exact ⟨w, n, hn⟩
    choose! w n hn using h
    refine ⟨P.sup n, ?_⟩
    obtain ⟨R', hR', hv', hact', hlate, hcross⟩ := exists_run π (fun _ => v) Finset.univ P (P.sup n)
    have hcmp := compare (T := P.sup n) ⟨hRr, hval, hact, hina, hT⟩ hR' (fun i _ => by rw [hv'])
      (fun i _ k hk => (hact' i k).2 ⟨Finset.mem_univ _, hk⟩)
      (by
        intro k hk j hj s m s₂ hs h1 hr
        exact hlate k s j m s₂ hs (by omega) hr (Or.inl ⟨fun _ => hj, fun _ => hk⟩))
      (by
        intro i hi k hk s n' hn' hd
        have := hcross i k s n' hd (fun h => hk (h.2 hi))
        omega)
    have hFS' : FailStop Finset.univ R' :=
      ⟨fun i _ k hk => (hact' i k).2 ⟨Finset.mem_univ _, hk⟩, fun i hi => absurd (Finset.mem_univ i) hi⟩
    have hAl' : cm.Allowed π R' := by
      refine allowed_of_late hcm (P.sup n) ?_
      intro k s j m s₂ hs hlt hT hr
      exact hlate k s j m s₂ hs hlt hr (Or.inr hT)
    have hUni := (hres Finset.univ (by simp) R' hR' hFS' hAl').2.2 rfl v (fun i => by rw [hv'])
    intro i hi
    have hle : n i ≤ P.sup n := Finset.le_sup (f := n) hi
    have hd' : DecidesAt π R' i (w i) (n i) :=
      decidesAt_congr (fun m hm => (hcmp i hi m (le_trans hm hle)).symm) (hn i hi)
    have hwv : w i = v := hUni i (w i) ⟨n i, hd'⟩
    exact ⟨n i, hle, hwv ▸ hn i hi⟩

theorem dls_scenario_A_core {N : ℕ} {σ M : Type} (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF)
    (htN : t ≤ N) (hres : Resilient π t cm) (P Q : Finset (Fin N)) (hdisj : Disjoint P Q)
    (hcover : P ∪ Q = Finset.univ) (hP1 : 1 ≤ P.card) (hPt : P.card ≤ t) (hQ1 : 1 ≤ Q.card)
    (hQt : Q.card ≤ t) :
    (∃ R : Run N σ, IsolatedScenario π P false R) ∧
    ∀ R : Run N σ, IsolatedScenario π P false R →
      ∃ TA : ℕ, ∀ i ∈ P, ∃ n ≤ TA, DecidesAt π R i false n :=
  scen_gen π t cm hcm hres P Q hdisj hcover hQt false

theorem dls_scenario_B_core {N : ℕ} {σ M : Type} (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF)
    (htN : t ≤ N) (hres : Resilient π t cm) (P Q : Finset (Fin N)) (hdisj : Disjoint P Q)
    (hcover : P ∪ Q = Finset.univ) (hP1 : 1 ≤ P.card) (hPt : P.card ≤ t) (hQ1 : 1 ≤ Q.card)
    (hQt : Q.card ≤ t) :
    (∃ R : Run N σ, IsolatedScenario π Q true R) ∧
    ∀ R : Run N σ, IsolatedScenario π Q true R →
      ∃ TB : ℕ, ∀ i ∈ Q, ∃ n ≤ TB, DecidesAt π R i true n :=
  scen_gen π t cm hcm hres Q P hdisj.symm (by rw [Finset.union_comm]; exact hcover) hPt true

theorem dls_scenario_C_core {N : ℕ} {σ M : Type} (π : Protocol N σ M) (cm : Comm) (hcm : cm.WF)
    (P Q : Finset (Fin N)) (hdisj : Disjoint P Q) (hcover : P ∪ Q = Finset.univ)
    (RA RB : Run N σ) (hA : IsolatedScenario π P false RA) (hB : IsolatedScenario π Q true RB)
    (T : ℕ) :
    ∃ R : Run N σ, IsRun π R ∧ cm.Allowed π R ∧ FailStop Finset.univ R ∧
      (∀ i ∈ P, R.val i = false) ∧ (∀ i ∈ Q, R.val i = true) ∧
      TimeOneWithin π P R ∧ TimeOneWithin π Q R ∧
      (∀ k i s n, (k, s) ∈ R.deliv i n → (k ∈ P ↔ i ∈ Q) → T < n) ∧
      (∀ i ∈ P, ∀ n ≤ T, R.state i n = RA.state i n) ∧
      (∀ i ∈ Q, ∀ n ≤ T, R.state i n = RB.state i n) := by
  have hPQ : ∀ i, i ∈ P ↔ i ∉ Q := by
    intro i
    constructor
    · intro h h'; exact Finset.disjoint_left.1 hdisj h h'
    · intro h
      have : i ∈ P ∪ Q := by rw [hcover]; exact Finset.mem_univ i
      rcases Finset.mem_union.1 this with h1 | h1
      · exact h1
      · exact absurd h1 h
  obtain ⟨R, hR, hv, hact, hlate, hcross⟩ :=
    exists_run π (fun i => if i ∈ P then false else true) Finset.univ P T
  have hvP : ∀ i ∈ P, R.val i = false := by
    intro i hi; rw [hv]; simp [hi]
  have hvQ : ∀ i ∈ Q, R.val i = true := by
    intro i hi
    have : i ∉ P := fun h => (hPQ i).1 h hi
    rw [hv]; simp [this]
  have hTP : TimeOneWithin π P R := by
    intro k hk j hj s m s₂ hs h1 hr
    exact hlate k s j m s₂ hs (by omega) hr (Or.inl ⟨fun _ => hj, fun _ => hk⟩)
  have hTQ : TimeOneWithin π Q R := by
    intro k hk j hj s m s₂ hs h1 hr
    have h1' : k ∉ P := fun h => (hPQ k).1 h hk
    have h2' : j ∉ P := fun h => (hPQ j).1 h hj
    exact hlate k s j m s₂ hs (by omega) hr (Or.inl ⟨fun h => absurd h h1', fun h => absurd h h2'⟩)
  have hcr : ∀ k i s n, (k, s) ∈ R.deliv i n → (k ∈ P ↔ i ∈ Q) → T < n := by
    intro k i s n hd hki
    refine hcross i k s n hd ?_
    intro h
    have h1 := hPQ i
    tauto
  refine ⟨R, hR, ?_, ⟨fun i _ k hk => (hact i k).2 ⟨Finset.mem_univ _, hk⟩,
    fun i hi => absurd (Finset.mem_univ i) hi⟩, hvP, hvQ, hTP, hTQ, hcr, ?_, ?_⟩
  · refine allowed_of_late hcm T ?_
    intro k s j m s₂ hs hlt hT hr
    exact hlate k s j m s₂ hs hlt hr (Or.inr hT)
  · exact compare (T := T) hA hR hvP
      (fun i _ k hk => (hact i k).2 ⟨Finset.mem_univ _, hk⟩) hTP
      (by
        intro i hi k hk s n' hn' hd
        have := hcross i k s n' hd (fun h => hk (h.2 hi))
        omega)
  · exact compare (T := T) hB hR hvQ
      (fun i _ k hk => (hact i k).2 ⟨Finset.mem_univ _, hk⟩) hTQ
      (by
        intro i hi k hk s n' hn' hd
        have h1 := hPQ k
        have h2 := hPQ i
        have := hcross i k s n' hd (by tauto)
        omega)

theorem dls_thm43_core (N t : ℕ) (hN : 2 ≤ N) (hNt : N ≤ 2 * t) (htN : t ≤ N) :
    (∀ Δ : ℕ, 0 < Δ → ∀ (σ M : Type) (π : Protocol N σ M),
      ¬ Resilient π t (Comm.eventually Δ)) ∧
    (∀ (σ M : Type) (π : Protocol N σ M), ¬ Resilient π t Comm.unknown) := by
  have key : ∀ (σ M : Type) (π : Protocol N σ M) (cm : Comm), cm.WF → ¬ Resilient π t cm := by
    intro σ M π cm hcm hres
    obtain ⟨P, -, hPcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N)))
      (n := N / 2) (by simp; omega)
    set Q : Finset (Fin N) := Finset.univ \ P with hQdef
    have hdisj : Disjoint P Q := Finset.disjoint_sdiff
    have hcover : P ∪ Q = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ P)
    have hcard : P.card + Q.card = N := by
      rw [← Finset.card_union_of_disjoint hdisj, hcover]; simp
    have hP1 : 1 ≤ P.card := by omega
    have hPt : P.card ≤ t := by omega
    have hQ1 : 1 ≤ Q.card := by omega
    have hQt : Q.card ≤ t := by omega
    obtain ⟨⟨RA, hRA⟩, hA2⟩ := dls_scenario_A_core π t cm hcm htN hres P Q hdisj hcover hP1 hPt hQ1 hQt
    obtain ⟨⟨RB, hRB⟩, hB2⟩ := dls_scenario_B_core π t cm hcm htN hres P Q hdisj hcover hP1 hPt hQ1 hQt
    obtain ⟨TA, hTA⟩ := hA2 RA hRA
    obtain ⟨TB, hTB⟩ := hB2 RB hRB
    obtain ⟨R, hR, hAl, hFS, -, -, -, -, -, hPs, hQs⟩ :=
      dls_scenario_C_core π cm hcm P Q hdisj hcover RA RB hRA hRB (max TA TB)
    obtain ⟨i, hi⟩ : P.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨j, hj⟩ : Q.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨n1, hn1, hd1⟩ := hTA i hi
    obtain ⟨n2, hn2, hd2⟩ := hTB j hj
    have hd1' : DecidesAt π R i false n1 :=
      decidesAt_congr (fun m hm => (hPs i hi m (by omega)).symm) hd1
    have hd2' : DecidesAt π R j true n2 :=
      decidesAt_congr (fun m hm => (hQs j hj m (by omega)).symm) hd2
    have hcc := (hres Finset.univ (by simp) R hR hFS hAl).1 i (Finset.mem_univ _) j
      (Finset.mem_univ _) false true ⟨n1, hd1'⟩ ⟨n2, hd2'⟩
    exact absurd hcc (by decide)
  exact ⟨fun Δ hΔ σ M π => key σ M π _ hΔ, fun σ M π => key σ M π _ trivial⟩

end DLSConsensus.LowerBound

open DLSConsensus.LowerBound


theorem solution (N t : ℕ) (hN : 2 ≤ N) (hNt : N ≤ 2 * t) (htN : t ≤ N) :
    (∀ Δ : ℕ, 0 < Δ → ∀ (σ M : Type) (π : Protocol N σ M),
      ¬ Resilient π t (Comm.eventually Δ)) ∧
    (∀ (σ M : Type) (π : Protocol N σ M), ¬ Resilient π t Comm.unknown) := by
  exact dls_thm43_core N t hN hNt htN
