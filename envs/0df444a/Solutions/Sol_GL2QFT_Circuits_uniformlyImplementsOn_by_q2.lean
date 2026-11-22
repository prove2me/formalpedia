-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_by_q2
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:57:22.151397+00:00
-- url     : https://prove2.me/submissions/39187add-0b90-4816-b7c9-b2eb89ff59dc

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_ByQ2_Aux

open Turing StateTransition

instance instDecEqFinTM2K (P : FinTM2) : DecidableEq P.K := P.kDecidableEq
instance instFintypeFinTM2K (P : FinTM2) : Fintype P.K := P.kFin
instance instFintypeFinTM2L (P : FinTM2) : Fintype P.Λ := P.ΛFin
instance instFintypeFinTM2S (P : FinTM2) : Fintype P.σ := P.σFin

def q2Prefix : Str := [true, false, true, true, false, false, true, true, false, false]

lemma encBin_two : LocalHamiltonian.encBin 2 = [true, false, true, true, false, false] := by
  decide

lemma encBin_one : LocalHamiltonian.encBin 1 = [true, true, false, false] := by
  decide

lemma q2Prefix_eq : q2Prefix = LocalHamiltonian.encBin 2 ++ LocalHamiltonian.encBin 1 := by
  decide

def isQ2Prefix (s : Str) : Bool := decide (s.take 10 = q2Prefix)

def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

lemma bitsVal_bits (n : ℕ) : bitsVal n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn, bitsVal, ih, Nat.bit_val]
      omega

lemma bits_inj {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  rw [← bitsVal_bits a, ← bitsVal_bits b, h]

lemma encBin_bits_append_inj (bs₁ bs₂ t₁ t₂ : Str)
    (h : (bs₁.flatMap (fun β => [true, β]) ++ [false, false]) ++ t₁ =
      (bs₂.flatMap (fun β => [true, β]) ++ [false, false]) ++ t₂) :
    bs₁ = bs₂ ∧ t₁ = t₂ := by
  induction bs₁ generalizing bs₂ with
  | nil =>
      cases bs₂ with
      | nil =>
          simp only [List.flatMap_nil, List.nil_append, List.cons_append, List.cons.injEq,
            true_and] at h
          exact ⟨rfl, h⟩
      | cons b₂ bs₂ =>
          simp at h
  | cons b₁ bs₁ ih =>
      cases bs₂ with
      | nil =>
          simp at h
      | cons b₂ bs₂ =>
          change true :: b₁ :: ((bs₁.flatMap (fun β => [true, β]) ++ [false, false]) ++ t₁) =
            true :: b₂ :: ((bs₂.flatMap (fun β => [true, β]) ++ [false, false]) ++ t₂) at h
          injection h with _ h1
          injection h1 with hb h2
          have ⟨hbs, ht⟩ := ih bs₂ h2
          exact ⟨congrArg₂ List.cons hb hbs, ht⟩

lemma encBin_append_inj {a b : ℕ} {t₁ t₂ : Str}
    (h : LocalHamiltonian.encBin a ++ t₁ = LocalHamiltonian.encBin b ++ t₂) :
    a = b ∧ t₁ = t₂ := by
  unfold LocalHamiltonian.encBin at h
  have ⟨hb, ht⟩ := encBin_bits_append_inj a.bits b.bits t₁ t₂ h
  exact ⟨bits_inj hb, ht⟩

lemma q_eq_two_iff (D : FieldData) : D.q = 2 ↔ D.p = 2 ∧ D.r = 1 := by
  constructor
  · intro hq
    unfold FieldData.q at hq
    have hdvd : D.p ∣ 2 := hq ▸ dvd_pow_self D.p D.hr.ne'
    have hp2 : D.p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left D.hp.ne_one
    have hr1 : D.r = 1 := by
      rw [hp2] at hq
      exact Nat.pow_right_injective (by decide : 1 < 2) (hq.trans (pow_one 2).symm)
    exact ⟨hp2, hr1⟩
  · rintro ⟨hp, hr⟩
    unfold FieldData.q
    rw [hp, hr, pow_one]

lemma isQ2Prefix_encData (D : FieldData) (k : ℕ) :
    isQ2Prefix (D.encData ++ encNat k) = true ↔ D.q = 2 := by
  unfold isQ2Prefix
  rw [decide_eq_true_eq]
  constructor
  · intro htake
    have hs : D.encData ++ encNat k =
        LocalHamiltonian.encBin 2 ++
          (LocalHamiltonian.encBin 1 ++ (D.encData ++ encNat k).drop 10) := by
      have htd : (D.encData ++ encNat k).take 10 ++ (D.encData ++ encNat k).drop 10 =
          D.encData ++ encNat k := List.take_append_drop 10 _
      change (D.encData ++ encNat k).take 10 = q2Prefix at htake
      rw [htake, q2Prefix_eq, List.append_assoc] at htd
      exact htd.symm
    have henc : D.encData ++ encNat k = LocalHamiltonian.encBin D.p ++ (LocalHamiltonian.encBin D.r ++
        (((List.range (D.r + 1)).flatMap fun j => LocalHamiltonian.encBin (D.f.coeff j).val) ++
          ((List.range 3).flatMap fun j =>
            (List.range D.r).flatMap fun l => LocalHamiltonian.encBin (D.digit (D.F.coeff j) l)) ++
          ((List.range 2).flatMap fun j =>
            (List.range D.r).flatMap fun l =>
              LocalHamiltonian.encBin
                (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff j) l)) ++
          encNat k)) := by
      simp [FieldData.encData, List.append_assoc]
    rw [henc] at hs
    have h1 := encBin_append_inj hs
    have h2 := encBin_append_inj h1.2
    exact (q_eq_two_iff D).mpr ⟨h1.1, h2.1⟩
  · intro hq
    obtain ⟨hp, hr⟩ := (q_eq_two_iff D).mp hq
    have hpre : LocalHamiltonian.encBin D.p ++ LocalHamiltonian.encBin D.r = q2Prefix := by
      rw [hp, hr, ← q2Prefix_eq]
    have hs : D.encData ++ encNat k = q2Prefix ++
        (((List.range (D.r + 1)).flatMap fun j => LocalHamiltonian.encBin (D.f.coeff j).val) ++
          ((List.range 3).flatMap fun j =>
            (List.range D.r).flatMap fun l => LocalHamiltonian.encBin (D.digit (D.F.coeff j) l)) ++
          ((List.range 2).flatMap fun j =>
            (List.range D.r).flatMap fun l =>
              LocalHamiltonian.encBin
                (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff j) l)) ++
          encNat k) := by
      unfold FieldData.encData
      simp only [List.append_assoc]
      rw [← List.append_assoc (LocalHamiltonian.encBin D.p), hpre]
    rw [hs, List.take_left' (by decide : q2Prefix.length = 10)]

section Growth

def stmtPushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtPushes q
  | .peek _ _ q => stmtPushes q
  | .pop _ _ q => stmtPushes q
  | .load _ q => stmtPushes q
  | .branch _ q r => max (stmtPushes q) (stmtPushes r)
  | .goto _ => 0
  | .halt => 0

def tmVolume {K : Type} [Fintype K] {Γ : K → Type} (s : ∀ k, List (Γ k)) : ℕ :=
  ∑ k : K, (s k).length

lemma tmVolume_update {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
    (s : ∀ k, List (Γ k)) (k : K) (v : List (Γ k)) :
    tmVolume (Function.update s k v) + (s k).length = tmVolume s + v.length := by
  unfold tmVolume
  have he : (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
    funext j
    by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length) (Finset.mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

lemma stepAux_tmVolume {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (s : ∀ k, List (Γ k)) :
    tmVolume (TM2.stepAux q v s).stk ≤ tmVolume s + stmtPushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (Function.update s k (g v :: s k))
      have hv := tmVolume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux, stmtPushes, Nat.add_assoc] using (by omega :
        tmVolume (TM2.stepAux q v (Function.update s k (g v :: s k))).stk ≤
          tmVolume s + (1 + stmtPushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (Function.update s k (s k).tail)
      have hv := tmVolume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux, stmtPushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux, hg, Bool.cond_false, stmtPushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (stmtPushes q) _) _)
      · simpa only [TM2.stepAux, hg, Bool.cond_true, stmtPushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (stmtPushes r)) _)
  | goto g => simp [TM2.stepAux, stmtPushes]
  | halt => simp [TM2.stepAux, stmtPushes]

def tmGrowth (P : FinTM2) : ℕ := ∑ l : P.Λ, stmtPushes (P.m l)

lemma step_tmVolume (P : FinTM2) (a b : P.Cfg) (h : P.step a = some b) :
    tmVolume b.stk ≤ tmVolume a.stk + tmGrowth P := by
  rcases a with ⟨l, v, s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b = TM2.stepAux (P.m l) v s := (Option.some.inj h).symm
      rw [hb]
      have hsingle : stmtPushes (P.m l) ≤ tmGrowth P :=
        Finset.single_le_sum (f := fun x => stmtPushes (P.m x)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ l)
      exact (stepAux_tmVolume _ _ _).trans (Nat.add_le_add_left hsingle _)

lemma iterate_tmVolume (P : FinTM2) :
    ∀ (t : ℕ) (a b : P.Cfg),
      (flip bind P.step)^[t] (some a) = some b →
      tmVolume b.stk ≤ tmVolume a.stk + t * tmGrowth P
  | 0, a, b, h => by
      have hab : a = b := Option.some.inj h
      subst b
      simp
  | t + 1, a, b, h => by
      rw [Function.iterate_succ_apply] at h
      cases hc : P.step a with
      | none =>
          have hnone : ∀ n : ℕ, (flip bind P.step)^[n] (none : Option P.Cfg) = none := by
            intro n; induction n with
            | zero => rfl
            | succ n ih => rw [Function.iterate_succ_apply]; exact ih
          change (flip bind P.step)^[t] (P.step a) = some b at h
          rw [hc, hnone] at h
          cases h
      | some c =>
          have hbc : (flip bind P.step)^[t] (some c) = some b := by
            change (flip bind P.step)^[t] (P.step a) = some b at h
            rwa [hc] at h
          have ih := iterate_tmVolume P t c b hbc
          have hs := step_tmVolume P a c hc
          rw [Nat.add_mul, one_mul]
          omega

lemma tmVolume_initList (P : FinTM2) (l : List (P.Γ P.k₀)) :
    tmVolume (initList P l).stk = l.length := by
  unfold tmVolume
  rw [Finset.sum_eq_single P.k₀]
  · simp [initList]
  · intro k _ hk
    simp [initList, hk]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma tmVolume_haltList (P : FinTM2) (l : List (P.Γ P.k₁)) :
    tmVolume (haltList P l).stk = l.length := by
  unfold tmVolume
  rw [Finset.sum_eq_single P.k₁]
  · simp [haltList]
  · intro k _ hk
    simp [haltList, hk]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma tm2_output_length {g : Str → Str}
    (M : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g) (s : Str) :
    (g s).length ≤ s.length + M.time.eval s.length * tmGrowth M.tm := by
  have hout := M.outputsFun s
  have hv := iterate_tmVolume M.tm hout.steps _ _ hout.evals_in_steps
  rw [tmVolume_initList, tmVolume_haltList] at hv
  simp only [id_eq, List.length_map] at hv hout
  have hle := Nat.mul_le_mul_right (tmGrowth M.tm) hout.steps_le_m
  omega

end Growth

section CombinedTM

inductive CombK (K₂ Kgt₂ : Type) where
  | inp | out | tmp | left (k : K₂) | right (k : Kgt₂)
  deriving DecidableEq

def combKEquiv (K₂ Kgt₂ : Type) : CombK K₂ Kgt₂ ≃ Unit ⊕ Unit ⊕ Unit ⊕ K₂ ⊕ Kgt₂ where
  toFun
    | .inp => .inl ()
    | .out => .inr (.inl ())
    | .tmp => .inr (.inr (.inl ()))
    | .left k => .inr (.inr (.inr (.inl k)))
    | .right k => .inr (.inr (.inr (.inr k)))
  invFun
    | .inl _ => .inp
    | .inr (.inl _) => .out
    | .inr (.inr (.inl _)) => .tmp
    | .inr (.inr (.inr (.inl k))) => .left k
    | .inr (.inr (.inr (.inr k))) => .right k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | k | k <;> rfl

instance instFintypeCombK (K₂ Kgt₂ : Type) [Fintype K₂] [Fintype Kgt₂] :
    Fintype (CombK K₂ Kgt₂) :=
  Fintype.ofEquiv _ (combKEquiv K₂ Kgt₂).symm

abbrev CombΓ (P₂ Pgt₂ : FinTM2) : CombK P₂.K Pgt₂.K → Type
  | .inp => Bool
  | .out => Bool
  | .tmp => Bool
  | .left k => P₂.Γ k
  | .right k => Pgt₂.Γ k

inductive CombΛ (Λ₂ Λgt₂ : Type) where
  | scan (i : Fin 10)
  | copy (ok : Bool)
  | push (ok : Bool)
  | runLeft (l : Λ₂)
  | runRight (l : Λgt₂)
  | drainRev (ok : Bool)
  | drainOut

def combΛEquiv (Λ₂ Λgt₂ : Type) :
    CombΛ Λ₂ Λgt₂ ≃ Fin 10 ⊕ Bool ⊕ Bool ⊕ Λ₂ ⊕ Λgt₂ ⊕ Bool ⊕ Unit where
  toFun
    | .scan i => .inl i
    | .copy ok => .inr (.inl ok)
    | .push ok => .inr (.inr (.inl ok))
    | .runLeft l => .inr (.inr (.inr (.inl l)))
    | .runRight l => .inr (.inr (.inr (.inr (.inl l))))
    | .drainRev ok => .inr (.inr (.inr (.inr (.inr (.inl ok)))))
    | .drainOut => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  invFun
    | .inl i => .scan i
    | .inr (.inl ok) => .copy ok
    | .inr (.inr (.inl ok)) => .push ok
    | .inr (.inr (.inr (.inl l))) => .runLeft l
    | .inr (.inr (.inr (.inr (.inl l)))) => .runRight l
    | .inr (.inr (.inr (.inr (.inr (.inl ok))))) => .drainRev ok
    | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .drainOut
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with i | ok | ok | l | l | ok | u <;> rfl

instance instFintypeCombΛ (Λ₂ Λgt₂ : Type) [Fintype Λ₂] [Fintype Λgt₂] :
    Fintype (CombΛ Λ₂ Λgt₂) :=
  Fintype.ofEquiv _ (combΛEquiv Λ₂ Λgt₂).symm

abbrev Combσ (σ₂ σgt₂ : Type) := Option Bool × σ₂ × σgt₂

def targetBit (i : Fin 10) : Bool :=
  q2Prefix[i.val]'(by simp only [q2Prefix, List.length_cons, List.length_nil]; exact i.isLt)

section Build
variable {f₂ fgt₂ : Str → Str}
variable (M₂ : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f₂)
variable (Mgt₂ : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) fgt₂)

def embedLeftStmt :
    TM2.Stmt M₂.tm.Γ M₂.tm.Λ M₂.tm.σ →
      TM2.Stmt (CombΓ M₂.tm Mgt₂.tm) (CombΛ M₂.tm.Λ Mgt₂.tm.Λ) (Combσ M₂.tm.σ Mgt₂.tm.σ)
  | .push k f q => .push (.left k) (fun v => f v.2.1) (embedLeftStmt q)
  | .peek k f q => .peek (.left k) (fun v x => (v.1, f v.2.1 x, v.2.2)) (embedLeftStmt q)
  | .pop k f q => .pop (.left k) (fun v x => (v.1, f v.2.1 x, v.2.2)) (embedLeftStmt q)
  | .load f q => .load (fun v => (v.1, f v.2.1, v.2.2)) (embedLeftStmt q)
  | .branch f q r => .branch (fun v => f v.2.1) (embedLeftStmt q) (embedLeftStmt r)
  | .goto f => .goto (fun v => .runLeft (f v.2.1))
  | .halt => .goto (fun _ => .drainRev true)

def embedRightStmt :
    TM2.Stmt Mgt₂.tm.Γ Mgt₂.tm.Λ Mgt₂.tm.σ →
      TM2.Stmt (CombΓ M₂.tm Mgt₂.tm) (CombΛ M₂.tm.Λ Mgt₂.tm.Λ) (Combσ M₂.tm.σ Mgt₂.tm.σ)
  | .push k f q => .push (.right k) (fun v => f v.2.2) (embedRightStmt q)
  | .peek k f q => .peek (.right k) (fun v x => (v.1, v.2.1, f v.2.2 x)) (embedRightStmt q)
  | .pop k f q => .pop (.right k) (fun v x => (v.1, v.2.1, f v.2.2 x)) (embedRightStmt q)
  | .load f q => .load (fun v => (v.1, v.2.1, f v.2.2)) (embedRightStmt q)
  | .branch f q r => .branch (fun v => f v.2.2) (embedRightStmt q) (embedRightStmt r)
  | .goto f => .goto (fun v => .runRight (f v.2.2))
  | .halt => .goto (fun _ => .drainRev false)

def combCode :
    CombΛ M₂.tm.Λ Mgt₂.tm.Λ →
      TM2.Stmt (CombΓ M₂.tm Mgt₂.tm) (CombΛ M₂.tm.Λ Mgt₂.tm.Λ) (Combσ M₂.tm.σ Mgt₂.tm.σ)
  | .scan i =>
      .pop .inp (fun v b => (b, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push .tmp (fun v => v.1.getD false)
            (.branch (fun v => decide (v.1.getD false = targetBit i))
              (.load (fun v => (none, v.2.1, v.2.2))
                (.goto (fun _ => if h : i.val + 1 < 10 then .scan ⟨i.val + 1, h⟩ else .copy true)))
              (.load (fun v => (none, v.2.1, v.2.2))
                (.goto (fun _ => .copy false)))))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => .push false))))
  | .copy ok =>
      .pop .inp (fun v b => (b, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push .tmp (fun v => v.1.getD false)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => .copy ok))))
          (.load (fun v => (none, v.2.1, v.2.2))
            (.goto (fun _ => .push ok))))
  | .push true =>
      .pop .tmp (fun v b => (b, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push (.left M₂.tm.k₀) (fun v => M₂.inputAlphabet.symm (v.1.getD false))
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => .push true))))
          (.load (fun _ => (none, M₂.tm.initialState, Mgt₂.tm.initialState))
            (.goto (fun _ => .runLeft M₂.tm.main))))
  | .push false =>
      .pop .tmp (fun v b => (b, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push (.right Mgt₂.tm.k₀) (fun v => Mgt₂.inputAlphabet.symm (v.1.getD false))
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => .push false))))
          (.load (fun _ => (none, M₂.tm.initialState, Mgt₂.tm.initialState))
            (.goto (fun _ => .runRight Mgt₂.tm.main))))
  | .runLeft l => embedLeftStmt M₂ Mgt₂ (M₂.tm.m l)
  | .runRight l => embedRightStmt M₂ Mgt₂ (Mgt₂.tm.m l)
  | .drainRev true =>
      .pop (.left M₂.tm.k₁) (fun v x => (x.map M₂.outputAlphabet, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push .tmp (fun v => v.1.getD false)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => .drainRev true))))
          (.load (fun _ => (none, M₂.tm.initialState, Mgt₂.tm.initialState))
            (.goto (fun _ => .drainOut))))
  | .drainRev false =>
      .pop (.right Mgt₂.tm.k₁) (fun v x => (x.map Mgt₂.outputAlphabet, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push .tmp (fun v => v.1.getD false)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => .drainRev false))))
          (.load (fun _ => (none, M₂.tm.initialState, Mgt₂.tm.initialState))
            (.goto (fun _ => .drainOut))))
  | .drainOut =>
      .pop .tmp (fun v b => (b, v.2.1, v.2.2))
        (.branch (fun v => v.1.isSome)
          (.push .out (fun v => v.1.getD false)
            (.load (fun v => (none, v.2.1, v.2.2))
              (.goto (fun _ => .drainOut))))
          (.load (fun _ => (none, M₂.tm.initialState, Mgt₂.tm.initialState))
            .halt))

abbrev combTM : FinTM2 where
  K := CombK M₂.tm.K Mgt₂.tm.K
  k₀ := .inp
  k₁ := .out
  Γ := CombΓ M₂.tm Mgt₂.tm
  Λ := CombΛ M₂.tm.Λ Mgt₂.tm.Λ
  main := .scan 0
  σ := Combσ M₂.tm.σ Mgt₂.tm.σ
  initialState := (none, M₂.tm.initialState, Mgt₂.tm.initialState)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := combCode M₂ Mgt₂

abbrev s₀ : Combσ M₂.tm.σ Mgt₂.tm.σ := (none, M₂.tm.initialState, Mgt₂.tm.initialState)

def combCfg (l : Option (CombΛ M₂.tm.Λ Mgt₂.tm.Λ)) (v : Combσ M₂.tm.σ Mgt₂.tm.σ)
    (stk : ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)) : (combTM M₂ Mgt₂).Cfg :=
  ⟨l, v, stk⟩

lemma combCfg_ext {c₁ c₂ : (combTM M₂ Mgt₂).Cfg}
    (hl : c₁.l = c₂.l) (hv : c₁.var = c₂.var) (hs : ∀ k, c₁.stk k = c₂.stk k) :
    c₁ = c₂ := by
  dsimp only [FinTM2.Cfg] at c₁ c₂
  rcases c₁ with ⟨l₁, v₁, s₁⟩
  rcases c₂ with ⟨l₂, v₂, s₂⟩
  dsimp only at hl hv hs
  subst hl hv
  congr 1
  exact funext hs

def stkInpTmp (xs ys : List Bool) : ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .inp => xs
  | .tmp => ys
  | _ => []

def stkTmpLeft (ys : List Bool) (ls : List (M₂.tm.Γ M₂.tm.k₀)) :
    ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .tmp => ys
  | .left k => if h : k = M₂.tm.k₀ then h ▸ ls else []
  | _ => []

def stkTmpRight (ys : List Bool) (rs : List (Mgt₂.tm.Γ Mgt₂.tm.k₀)) :
    ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .tmp => ys
  | .right k => if h : k = Mgt₂.tm.k₀ then h ▸ rs else []
  | _ => []

def stkLeft (S : ∀ k, List (M₂.tm.Γ k)) : ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .left k => S k
  | _ => []

def stkRight (S : ∀ k, List (Mgt₂.tm.Γ k)) : ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .right k => S k
  | _ => []

def stkLeftOut (ls : List (M₂.tm.Γ M₂.tm.k₁)) (ys : List Bool) :
    ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .left k => if h : k = M₂.tm.k₁ then h ▸ ls else []
  | .tmp => ys
  | _ => []

def stkRightOut (rs : List (Mgt₂.tm.Γ Mgt₂.tm.k₁)) (ys : List Bool) :
    ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .right k => if h : k = Mgt₂.tm.k₁ then h ▸ rs else []
  | .tmp => ys
  | _ => []

def stkOut (ys zs : List Bool) : ∀ k, List (CombΓ M₂.tm Mgt₂.tm k)
  | .tmp => ys
  | .out => zs
  | _ => []

lemma update_stkInpTmp_inp (xs ys xs' : List Bool) :
    Function.update (stkInpTmp M₂ Mgt₂ xs ys) .inp xs' = stkInpTmp M₂ Mgt₂ xs' ys := by
  funext k
  cases k with
  | inp => dsimp only [Function.update, stkInpTmp]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkInpTmp]; exact dif_neg (by intro h; cases h)

lemma update_stkInpTmp_tmp (xs ys ys' : List Bool) :
    Function.update (stkInpTmp M₂ Mgt₂ xs ys) .tmp ys' = stkInpTmp M₂ Mgt₂ xs ys' := by
  funext k
  cases k with
  | tmp => dsimp only [Function.update, stkInpTmp]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkInpTmp]; exact dif_neg (by intro h; cases h)

lemma update_stkTmpLeft_tmp (ys ys' : List Bool) (ls : List (M₂.tm.Γ M₂.tm.k₀)) :
    Function.update (stkTmpLeft M₂ Mgt₂ ys ls) .tmp ys' = stkTmpLeft M₂ Mgt₂ ys' ls := by
  funext k
  cases k with
  | tmp => dsimp only [Function.update, stkTmpLeft]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkTmpLeft]; exact dif_neg (by intro h; cases h)

lemma update_stkTmpLeft_left (ys : List Bool) (ls ls' : List (M₂.tm.Γ M₂.tm.k₀)) :
    Function.update (stkTmpLeft M₂ Mgt₂ ys ls) (.left M₂.tm.k₀) ls' =
      stkTmpLeft M₂ Mgt₂ ys ls' := by
  funext k
  cases k with
  | left k' =>
      by_cases hk : k' = M₂.tm.k₀
      · subst hk
        dsimp only [Function.update, stkTmpLeft]
        rw [dif_pos (rfl : CombK.left M₂.tm.k₀ = CombK.left M₂.tm.k₀), dif_pos (rfl : M₂.tm.k₀ = M₂.tm.k₀)]
      · dsimp only [Function.update, stkTmpLeft]
        rw [dif_neg (by intro h; injection h with h'; exact hk h')]
        simp only [dif_neg hk]
  | _ => dsimp only [Function.update, stkTmpLeft]; exact dif_neg (by intro h; cases h)

lemma update_stkTmpRight_tmp (ys ys' : List Bool) (rs : List (Mgt₂.tm.Γ Mgt₂.tm.k₀)) :
    Function.update (stkTmpRight M₂ Mgt₂ ys rs) .tmp ys' = stkTmpRight M₂ Mgt₂ ys' rs := by
  funext k
  cases k with
  | tmp => dsimp only [Function.update, stkTmpRight]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkTmpRight]; exact dif_neg (by intro h; cases h)

lemma update_stkTmpRight_right (ys : List Bool) (rs rs' : List (Mgt₂.tm.Γ Mgt₂.tm.k₀)) :
    Function.update (stkTmpRight M₂ Mgt₂ ys rs) (.right Mgt₂.tm.k₀) rs' =
      stkTmpRight M₂ Mgt₂ ys rs' := by
  funext k
  cases k with
  | right k' =>
      by_cases hk : k' = Mgt₂.tm.k₀
      · subst hk
        dsimp only [Function.update, stkTmpRight]
        rw [dif_pos (rfl : CombK.right Mgt₂.tm.k₀ = CombK.right Mgt₂.tm.k₀),
          dif_pos (rfl : Mgt₂.tm.k₀ = Mgt₂.tm.k₀)]
      · dsimp only [Function.update, stkTmpRight]
        rw [dif_neg (by intro h; injection h with h'; exact hk h')]
        simp only [dif_neg hk]
  | _ => dsimp only [Function.update, stkTmpRight]; exact dif_neg (by intro h; cases h)

lemma update_stkLeft (S : ∀ k, List (M₂.tm.Γ k)) (k : M₂.tm.K) (v : List (M₂.tm.Γ k)) :
    Function.update (stkLeft M₂ Mgt₂ S) (.left k) v = stkLeft M₂ Mgt₂ (Function.update S k v) := by
  funext j
  cases j with
  | left j' =>
      by_cases hj : j' = k
      · subst hj
        dsimp only [Function.update, stkLeft]
        rw [dif_pos (rfl : CombK.left j' = CombK.left j'), dif_pos (rfl : j' = j')]
      · dsimp only [Function.update, stkLeft]
        rw [dif_neg (fun h => CombK.left.noConfusion h fun h' => hj (eq_of_heq h')), dif_neg hj]
  | _ => dsimp only [Function.update, stkLeft]; exact dif_neg (by intro h; cases h)

lemma update_stkRight (S : ∀ k, List (Mgt₂.tm.Γ k)) (k : Mgt₂.tm.K) (v : List (Mgt₂.tm.Γ k)) :
    Function.update (stkRight M₂ Mgt₂ S) (.right k) v = stkRight M₂ Mgt₂ (Function.update S k v) := by
  funext j
  cases j with
  | right j' =>
      by_cases hj : j' = k
      · subst hj
        dsimp only [Function.update, stkRight]
        rw [dif_pos (rfl : CombK.right j' = CombK.right j'), dif_pos (rfl : j' = j')]
      · dsimp only [Function.update, stkRight]
        rw [dif_neg (fun h => CombK.right.noConfusion h fun h' => hj (eq_of_heq h')), dif_neg hj]
  | _ => dsimp only [Function.update, stkRight]; exact dif_neg (by intro h; cases h)

lemma update_stkLeftOut_left (ls ls' : List (M₂.tm.Γ M₂.tm.k₁)) (ys : List Bool) :
    Function.update (stkLeftOut M₂ Mgt₂ ls ys) (.left M₂.tm.k₁) ls' =
      stkLeftOut M₂ Mgt₂ ls' ys := by
  funext k
  cases k with
  | left k' =>
      by_cases hk : k' = M₂.tm.k₁
      · subst hk
        dsimp only [Function.update, stkLeftOut]
        rw [dif_pos (rfl : CombK.left M₂.tm.k₁ = CombK.left M₂.tm.k₁), dif_pos (rfl : M₂.tm.k₁ = M₂.tm.k₁)]
      · dsimp only [Function.update, stkLeftOut]
        rw [dif_neg (by intro h; injection h with h'; exact hk h')]
        simp only [dif_neg hk]
  | _ => dsimp only [Function.update, stkLeftOut]; exact dif_neg (by intro h; cases h)

lemma update_stkLeftOut_tmp (ls : List (M₂.tm.Γ M₂.tm.k₁)) (ys ys' : List Bool) :
    Function.update (stkLeftOut M₂ Mgt₂ ls ys) .tmp ys' = stkLeftOut M₂ Mgt₂ ls ys' := by
  funext k
  cases k with
  | tmp => dsimp only [Function.update, stkLeftOut]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkLeftOut]; exact dif_neg (by intro h; cases h)

lemma update_stkRightOut_right (rs rs' : List (Mgt₂.tm.Γ Mgt₂.tm.k₁)) (ys : List Bool) :
    Function.update (stkRightOut M₂ Mgt₂ rs ys) (.right Mgt₂.tm.k₁) rs' =
      stkRightOut M₂ Mgt₂ rs' ys := by
  funext k
  cases k with
  | right k' =>
      by_cases hk : k' = Mgt₂.tm.k₁
      · subst hk
        dsimp only [Function.update, stkRightOut]
        rw [dif_pos (rfl : CombK.right Mgt₂.tm.k₁ = CombK.right Mgt₂.tm.k₁),
          dif_pos (rfl : Mgt₂.tm.k₁ = Mgt₂.tm.k₁)]
      · dsimp only [Function.update, stkRightOut]
        rw [dif_neg (by intro h; injection h with h'; exact hk h')]
        simp only [dif_neg hk]
  | _ => dsimp only [Function.update, stkRightOut]; exact dif_neg (by intro h; cases h)

lemma update_stkRightOut_tmp (rs : List (Mgt₂.tm.Γ Mgt₂.tm.k₁)) (ys ys' : List Bool) :
    Function.update (stkRightOut M₂ Mgt₂ rs ys) .tmp ys' = stkRightOut M₂ Mgt₂ rs ys' := by
  funext k
  cases k with
  | tmp => dsimp only [Function.update, stkRightOut]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkRightOut]; exact dif_neg (by intro h; cases h)

lemma update_stkOut_tmp (ys ys' zs : List Bool) :
    Function.update (stkOut M₂ Mgt₂ ys zs) .tmp ys' = stkOut M₂ Mgt₂ ys' zs := by
  funext k
  cases k with
  | tmp => dsimp only [Function.update, stkOut]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkOut]; exact dif_neg (by intro h; cases h)

lemma update_stkOut_out (ys zs zs' : List Bool) :
    Function.update (stkOut M₂ Mgt₂ ys zs) .out zs' = stkOut M₂ Mgt₂ ys zs' := by
  funext k
  cases k with
  | out => dsimp only [Function.update, stkOut]; exact dif_pos rfl
  | _ => dsimp only [Function.update, stkOut]; exact dif_neg (by intro h; cases h)

def step_one {P : FinTM2} {a b : P.Cfg} (h : P.step a = some b) :
    EvalsToInTime P.step a (some b) 1 :=
  ⟨⟨1, by change (flip bind P.step) (some a) = some b; exact h⟩, le_rfl⟩

def eval_copy (ok : Bool) (xs ys : List Bool) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some (.copy ok)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ xs ys))
      (some (combCfg M₂ Mgt₂ (some (.push ok)) (s₀ M₂ Mgt₂)
        (stkInpTmp M₂ Mgt₂ [] (xs.reverse ++ ys))))
      (xs.length + 1) := by
  induction xs generalizing ys with
  | nil =>
      refine step_one ?_
      change some (combCfg M₂ Mgt₂ (some (.push ok)) (s₀ M₂ Mgt₂)
        (Function.update (stkInpTmp M₂ Mgt₂ [] ys) .inp [])) = _
      rw [update_stkInpTmp_inp]
      simp only [List.reverse_nil, List.nil_append]
  | cons b xs ih =>
      have h1 : (combTM M₂ Mgt₂).step
          (combCfg M₂ Mgt₂ (some (.copy ok)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ (b :: xs) ys)) =
          some (combCfg M₂ Mgt₂ (some (.copy ok)) (s₀ M₂ Mgt₂)
            (stkInpTmp M₂ Mgt₂ xs (b :: ys))) := by
        change some (combCfg M₂ Mgt₂ (some (.copy ok)) (s₀ M₂ Mgt₂)
          (Function.update (Function.update (stkInpTmp M₂ Mgt₂ (b :: xs) ys) .inp xs) .tmp
            (b :: ys))) = _
        rw [update_stkInpTmp_inp, update_stkInpTmp_tmp]
      have h2 := EvalsToInTime.trans _ 1 (xs.length + 1) _ _ _ (step_one h1) (ih (b :: ys))
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        Nat.add_comm 1 (xs.length + 1)] using h2

def eval_scan (i : Fin 10) (xs ys : List Bool)
    (hlen : ys.length = i.val) (hpre : ys.reverse = q2Prefix.take i.val) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some (.scan i)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ xs ys))
      (some (combCfg M₂ Mgt₂ (some (.push (isQ2Prefix (ys.reverse ++ xs)))) (s₀ M₂ Mgt₂)
        (stkInpTmp M₂ Mgt₂ [] (xs.reverse ++ ys))))
      (xs.length + 1) := by
  induction xs generalizing i ys with
  | nil =>
      have hq : isQ2Prefix (ys.reverse ++ []) = false := by
        unfold isQ2Prefix
        rw [decide_eq_false_iff_not]
        intro heq
        have hl := congrArg List.length heq
        simp only [List.append_nil, List.length_take, List.length_reverse, hlen] at hl
        have hqlen : q2Prefix.length = 10 := by decide
        omega
      rw [hq]
      refine step_one ?_
      change some (combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂)
        (Function.update (stkInpTmp M₂ Mgt₂ [] ys) .inp [])) = _
      rw [update_stkInpTmp_inp]
      simp only [List.reverse_nil, List.nil_append]
  | cons b xs ih =>
      by_cases hb : b = targetBit i
      · by_cases hi : i.val + 1 < 10
        · have h1 : (combTM M₂ Mgt₂).step
              (combCfg M₂ Mgt₂ (some (.scan i)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ (b :: xs) ys)) =
              some (combCfg M₂ Mgt₂ (some (.scan ⟨i.val + 1, hi⟩)) (s₀ M₂ Mgt₂)
                (stkInpTmp M₂ Mgt₂ xs (b :: ys))) := by
            dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
            rw [show stkInpTmp M₂ Mgt₂ (b :: xs) ys CombK.inp = b :: xs from rfl]
            simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
              Bool.cond_true, dif_pos hi]
            rw [update_stkInpTmp_inp]
            rw [show stkInpTmp M₂ Mgt₂ xs ys CombK.tmp = ys from rfl]
            rw [update_stkInpTmp_tmp]
            simp only [hb, decide_true, Bool.cond_true]
          have hlen' : (b :: ys).length = i.val + 1 := by simp [hlen]
          have hpre' : (b :: ys).reverse = q2Prefix.take (i.val + 1) := by
            rw [List.reverse_cons, hpre, List.take_add_one]
            simp [targetBit, hb, show i.val < q2Prefix.length by simp [q2Prefix]]
          have h2 := EvalsToInTime.trans _ 1 (xs.length + 1) _ _ _ (step_one h1)
            (ih ⟨i.val + 1, hi⟩ (b :: ys) hlen' hpre')
          have heq : (b :: ys).reverse ++ xs = ys.reverse ++ (b :: xs) := by
            simp [List.reverse_cons]
          rw [heq] at h2
          simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Nat.add_comm 1 (xs.length + 1)] using h2
        · have hi9 : i.val = 9 := by omega
          have h1 : (combTM M₂ Mgt₂).step
              (combCfg M₂ Mgt₂ (some (.scan i)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ (b :: xs) ys)) =
              some (combCfg M₂ Mgt₂ (some (.copy true)) (s₀ M₂ Mgt₂)
                (stkInpTmp M₂ Mgt₂ xs (b :: ys))) := by
            dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
            rw [show stkInpTmp M₂ Mgt₂ (b :: xs) ys CombK.inp = b :: xs from rfl]
            simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
              Bool.cond_true, dif_neg hi]
            rw [update_stkInpTmp_inp]
            rw [show stkInpTmp M₂ Mgt₂ xs ys CombK.tmp = ys from rfl]
            rw [update_stkInpTmp_tmp]
            simp only [hb, decide_true, Bool.cond_true]
          have hpre' : (b :: ys).reverse = q2Prefix := by
            rw [List.reverse_cons, hpre]
            have htake : q2Prefix.take i.val ++ [targetBit i] = q2Prefix.take (i.val + 1) := by
              rw [List.take_add_one]
              simp [targetBit, show i.val < q2Prefix.length by simp [q2Prefix]]
            rw [hb, htake, hi9]
            decide
          have hq : isQ2Prefix (ys.reverse ++ (b :: xs)) = true := by
            have heq : ys.reverse ++ (b :: xs) = (b :: ys).reverse ++ xs := by
              simp [List.reverse_cons]
            rw [heq, hpre']
            unfold isQ2Prefix
            rw [decide_eq_true_eq, List.take_left' (by decide : q2Prefix.length = 10)]
          rw [hq]
          have h2 := EvalsToInTime.trans _ 1 (xs.length + 1) _ _ _ (step_one h1)
            (eval_copy M₂ Mgt₂ true xs (b :: ys))
          simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Nat.add_comm 1 (xs.length + 1)] using h2
      · have h1 : (combTM M₂ Mgt₂).step
            (combCfg M₂ Mgt₂ (some (.scan i)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ (b :: xs) ys)) =
            some (combCfg M₂ Mgt₂ (some (.copy false)) (s₀ M₂ Mgt₂)
              (stkInpTmp M₂ Mgt₂ xs (b :: ys))) := by
          dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
          rw [show stkInpTmp M₂ Mgt₂ (b :: xs) ys CombK.inp = b :: xs from rfl]
          simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
            Bool.cond_true]
          rw [update_stkInpTmp_inp]
          rw [show stkInpTmp M₂ Mgt₂ xs ys CombK.tmp = ys from rfl]
          rw [update_stkInpTmp_tmp]
          simp only [hb, decide_false, Bool.cond_false]
        have hq : isQ2Prefix (ys.reverse ++ (b :: xs)) = false := by
          unfold isQ2Prefix
          rw [decide_eq_false_iff_not]
          intro htake
          have hget := congrArg (fun l => l[i.val]?) htake
          have h10 : i.val < 10 := i.isLt
          have hql : i.val < q2Prefix.length := by
            simp only [q2Prefix, List.length_cons, List.length_nil]
            exact h10
          have hlen_rev : ys.reverse.length = i.val := by simp [hlen]
          rw [List.getElem?_take, if_pos h10, List.getElem?_append_right hlen_rev.le] at hget
          simp only [hlen_rev, Nat.sub_self, List.getElem?_cons_zero,
            List.getElem?_eq_getElem hql] at hget
          exact hb (Option.some.inj hget)
        rw [hq]
        have h2 := EvalsToInTime.trans _ 1 (xs.length + 1) _ _ _ (step_one h1)
          (eval_copy M₂ Mgt₂ false xs (b :: ys))
        simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append, Nat.add_comm 1 (xs.length + 1)] using h2

def eval_push_true (ys : List Bool) (ls : List (M₂.tm.Γ M₂.tm.k₀)) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some (.push true)) (s₀ M₂ Mgt₂) (stkTmpLeft M₂ Mgt₂ ys ls))
      (some (combCfg M₂ Mgt₂ (some (.runLeft M₂.tm.main)) (s₀ M₂ Mgt₂)
        (stkTmpLeft M₂ Mgt₂ [] (ys.reverse.map M₂.inputAlphabet.symm ++ ls))))
      (ys.length + 1) := by
  induction ys generalizing ls with
  | nil =>
      refine step_one ?_
      change some (combCfg M₂ Mgt₂ (some (.runLeft M₂.tm.main)) (s₀ M₂ Mgt₂)
        (Function.update (stkTmpLeft M₂ Mgt₂ [] ls) .tmp [])) = _
      rw [update_stkTmpLeft_tmp]
      simp only [List.reverse_nil, List.map_nil, List.nil_append]
  | cons b ys ih =>
      have h1 : (combTM M₂ Mgt₂).step
          (combCfg M₂ Mgt₂ (some (.push true)) (s₀ M₂ Mgt₂) (stkTmpLeft M₂ Mgt₂ (b :: ys) ls)) =
          some (combCfg M₂ Mgt₂ (some (.push true)) (s₀ M₂ Mgt₂)
            (stkTmpLeft M₂ Mgt₂ ys (M₂.inputAlphabet.symm b :: ls))) := by
        change some (combCfg M₂ Mgt₂ (some (.push true)) (s₀ M₂ Mgt₂)
          (Function.update (Function.update (stkTmpLeft M₂ Mgt₂ (b :: ys) ls) .tmp ys)
            (.left M₂.tm.k₀)
            (M₂.inputAlphabet.symm b :: stkTmpLeft M₂ Mgt₂ (b :: ys) ls (.left M₂.tm.k₀)))) = _
        have hstkl : stkTmpLeft M₂ Mgt₂ (b :: ys) ls (.left M₂.tm.k₀) = ls := by
          dsimp only [stkTmpLeft]; exact dif_pos rfl
        rw [hstkl, update_stkTmpLeft_tmp, update_stkTmpLeft_left]
      have h2 := EvalsToInTime.trans _ 1 (ys.length + 1) _ _ _ (step_one h1)
        (ih (M₂.inputAlphabet.symm b :: ls))
      simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append,
        Nat.add_comm 1 (ys.length + 1)] using h2

def eval_push_false (ys : List Bool) (rs : List (Mgt₂.tm.Γ Mgt₂.tm.k₀)) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂) (stkTmpRight M₂ Mgt₂ ys rs))
      (some (combCfg M₂ Mgt₂ (some (.runRight Mgt₂.tm.main)) (s₀ M₂ Mgt₂)
        (stkTmpRight M₂ Mgt₂ [] (ys.reverse.map Mgt₂.inputAlphabet.symm ++ rs))))
      (ys.length + 1) := by
  induction ys generalizing rs with
  | nil =>
      refine step_one ?_
      change some (combCfg M₂ Mgt₂ (some (.runRight Mgt₂.tm.main)) (s₀ M₂ Mgt₂)
        (Function.update (stkTmpRight M₂ Mgt₂ [] rs) .tmp [])) = _
      rw [update_stkTmpRight_tmp]
      simp only [List.reverse_nil, List.map_nil, List.nil_append]
  | cons b ys ih =>
      have h1 : (combTM M₂ Mgt₂).step
          (combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂) (stkTmpRight M₂ Mgt₂ (b :: ys) rs)) =
          some (combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂)
            (stkTmpRight M₂ Mgt₂ ys (Mgt₂.inputAlphabet.symm b :: rs))) := by
        change some (combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂)
          (Function.update (Function.update (stkTmpRight M₂ Mgt₂ (b :: ys) rs) .tmp ys)
            (.right Mgt₂.tm.k₀)
            (Mgt₂.inputAlphabet.symm b :: stkTmpRight M₂ Mgt₂ (b :: ys) rs (.right Mgt₂.tm.k₀)))) = _
        have hstkr : stkTmpRight M₂ Mgt₂ (b :: ys) rs (.right Mgt₂.tm.k₀) = rs := by
          dsimp only [stkTmpRight]; exact dif_pos rfl
        rw [hstkr, update_stkTmpRight_tmp, update_stkTmpRight_right]
      have h2 := EvalsToInTime.trans _ 1 (ys.length + 1) _ _ _ (step_one h1)
        (ih (Mgt₂.inputAlphabet.symm b :: rs))
      simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append,
        Nat.add_comm 1 (ys.length + 1)] using h2

def leftCfg (c : M₂.tm.Cfg) : (combTM M₂ Mgt₂).Cfg where
  l := match c.l with | none => some (.drainRev true) | some l => some (.runLeft l)
  var := (none, c.var, Mgt₂.tm.initialState)
  stk := stkLeft M₂ Mgt₂ c.stk

def rightCfg (c : Mgt₂.tm.Cfg) : (combTM M₂ Mgt₂).Cfg where
  l := match c.l with | none => some (.drainRev false) | some l => some (.runRight l)
  var := (none, M₂.tm.initialState, c.var)
  stk := stkRight M₂ Mgt₂ c.stk

lemma stepAux_embedLeft (q : TM2.Stmt M₂.tm.Γ M₂.tm.Λ M₂.tm.σ)
    (v : M₂.tm.σ) (S : ∀ k, List (M₂.tm.Γ k)) :
    TM2.stepAux (embedLeftStmt M₂ Mgt₂ q) (none, v, Mgt₂.tm.initialState) (stkLeft M₂ Mgt₂ S) =
      leftCfg M₂ Mgt₂ (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      dsimp only [embedLeftStmt, TM2.stepAux]
      rw [show stkLeft M₂ Mgt₂ S (CombK.left k) = S k from rfl, update_stkLeft]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      dsimp only [embedLeftStmt, TM2.stepAux]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      dsimp only [embedLeftStmt, TM2.stepAux]
      rw [show stkLeft M₂ Mgt₂ S (CombK.left k) = S k from rfl, update_stkLeft]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      dsimp only [embedLeftStmt, TM2.stepAux]
      exact ih (f v) S
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [embedLeftStmt, TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ihr v S
      · exact ihq v S
  | goto f => rfl
  | halt => rfl

lemma stepAux_embedRight (q : TM2.Stmt Mgt₂.tm.Γ Mgt₂.tm.Λ Mgt₂.tm.σ)
    (v : Mgt₂.tm.σ) (S : ∀ k, List (Mgt₂.tm.Γ k)) :
    TM2.stepAux (embedRightStmt M₂ Mgt₂ q) (none, M₂.tm.initialState, v) (stkRight M₂ Mgt₂ S) =
      rightCfg M₂ Mgt₂ (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      dsimp only [embedRightStmt, TM2.stepAux]
      rw [show stkRight M₂ Mgt₂ S (CombK.right k) = S k from rfl, update_stkRight]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      dsimp only [embedRightStmt, TM2.stepAux]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      dsimp only [embedRightStmt, TM2.stepAux]
      rw [show stkRight M₂ Mgt₂ S (CombK.right k) = S k from rfl, update_stkRight]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      dsimp only [embedRightStmt, TM2.stepAux]
      exact ih (f v) S
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [embedRightStmt, TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ihr v S
      · exact ihq v S
  | goto f => rfl
  | halt => rfl

lemma sim_left :
    ∀ (t : ℕ) (a b : M₂.tm.Cfg),
      (flip bind M₂.tm.step)^[t] (some a) = some b →
      (flip bind (combTM M₂ Mgt₂).step)^[t] (some (leftCfg M₂ Mgt₂ a)) =
        some (leftCfg M₂ Mgt₂ b)
  | 0, a, b, h => by
      have hab : a = b := Option.some.inj h
      subst b
      rfl
  | t + 1, a, b, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      cases hc : M₂.tm.step a with
      | none =>
          have hnone : ∀ n : ℕ, (flip bind M₂.tm.step)^[n] (none : Option M₂.tm.Cfg) = none := by
            intro n; induction n with
            | zero => rfl
            | succ n ih => rw [Function.iterate_succ_apply]; exact ih
          change (flip bind M₂.tm.step)^[t] (M₂.tm.step a) = some b at h
          rw [hc, hnone] at h
          cases h
      | some c =>
          have hbc : (flip bind M₂.tm.step)^[t] (some c) = some b := by
            change (flip bind M₂.tm.step)^[t] (M₂.tm.step a) = some b at h
            rwa [hc] at h
          have hstep : (combTM M₂ Mgt₂).step (leftCfg M₂ Mgt₂ a) = some (leftCfg M₂ Mgt₂ c) := by
            rcases a with ⟨l, v, S⟩
            cases l with
            | none => cases hc
            | some l =>
                have hceq : c = TM2.stepAux (M₂.tm.m l) v S := (Option.some.inj hc).symm
                rw [hceq]
                change some (TM2.stepAux (embedLeftStmt M₂ Mgt₂ (M₂.tm.m l))
                  (none, v, Mgt₂.tm.initialState) (stkLeft M₂ Mgt₂ S)) = _
                rw [stepAux_embedLeft]
                rfl
          change (flip bind (combTM M₂ Mgt₂).step)^[t]
            ((combTM M₂ Mgt₂).step (leftCfg M₂ Mgt₂ a)) = _
          rw [hstep]
          exact sim_left t c b hbc

lemma sim_right :
    ∀ (t : ℕ) (a b : Mgt₂.tm.Cfg),
      (flip bind Mgt₂.tm.step)^[t] (some a) = some b →
      (flip bind (combTM M₂ Mgt₂).step)^[t] (some (rightCfg M₂ Mgt₂ a)) =
        some (rightCfg M₂ Mgt₂ b)
  | 0, a, b, h => by
      have hab : a = b := Option.some.inj h
      subst b
      rfl
  | t + 1, a, b, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      cases hc : Mgt₂.tm.step a with
      | none =>
          have hnone : ∀ n : ℕ, (flip bind Mgt₂.tm.step)^[n] (none : Option Mgt₂.tm.Cfg) = none := by
            intro n; induction n with
            | zero => rfl
            | succ n ih => rw [Function.iterate_succ_apply]; exact ih
          change (flip bind Mgt₂.tm.step)^[t] (Mgt₂.tm.step a) = some b at h
          rw [hc, hnone] at h
          cases h
      | some c =>
          have hbc : (flip bind Mgt₂.tm.step)^[t] (some c) = some b := by
            change (flip bind Mgt₂.tm.step)^[t] (Mgt₂.tm.step a) = some b at h
            rwa [hc] at h
          have hstep : (combTM M₂ Mgt₂).step (rightCfg M₂ Mgt₂ a) = some (rightCfg M₂ Mgt₂ c) := by
            rcases a with ⟨l, v, S⟩
            cases l with
            | none => cases hc
            | some l =>
                have hceq : c = TM2.stepAux (Mgt₂.tm.m l) v S := (Option.some.inj hc).symm
                rw [hceq]
                change some (TM2.stepAux (embedRightStmt M₂ Mgt₂ (Mgt₂.tm.m l))
                  (none, M₂.tm.initialState, v) (stkRight M₂ Mgt₂ S)) = _
                rw [stepAux_embedRight]
                rfl
          change (flip bind (combTM M₂ Mgt₂).step)^[t]
            ((combTM M₂ Mgt₂).step (rightCfg M₂ Mgt₂ a)) = _
          rw [hstep]
          exact sim_right t c b hbc

def eval_drainRev_true (ls : List (M₂.tm.Γ M₂.tm.k₁)) (ys : List Bool) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some (.drainRev true)) (s₀ M₂ Mgt₂) (stkLeftOut M₂ Mgt₂ ls ys))
      (some (combCfg M₂ Mgt₂ (some .drainOut) (s₀ M₂ Mgt₂)
        (stkOut M₂ Mgt₂ (ls.reverse.map M₂.outputAlphabet ++ ys) [])))
      (ls.length + 1) := by
  induction ls generalizing ys with
  | nil =>
      refine step_one ?_
      dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
      rw [show stkLeftOut M₂ Mgt₂ [] ys (CombK.left M₂.tm.k₁) = [] from by
        dsimp only [stkLeftOut]; exact dif_pos rfl]
      simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
        Bool.cond_false, List.reverse_nil, List.map_nil, List.nil_append]
      rw [update_stkLeftOut_left]
      congr 2; funext k
      cases k with
      | left k' =>
          rcases eq_or_ne k' M₂.tm.k₁ with rfl | hk
          · dsimp only [stkLeftOut, stkOut]; exact dif_pos rfl
          · dsimp only [stkLeftOut, stkOut]; exact dif_neg hk
      | _ => rfl
  | cons a ls ih =>
      have h1 : (combTM M₂ Mgt₂).step
          (combCfg M₂ Mgt₂ (some (.drainRev true)) (s₀ M₂ Mgt₂) (stkLeftOut M₂ Mgt₂ (a :: ls) ys)) =
          some (combCfg M₂ Mgt₂ (some (.drainRev true)) (s₀ M₂ Mgt₂)
            (stkLeftOut M₂ Mgt₂ ls (M₂.outputAlphabet a :: ys))) := by
        dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
        rw [show stkLeftOut M₂ Mgt₂ (a :: ls) ys (CombK.left M₂.tm.k₁) = a :: ls from by
          dsimp only [stkLeftOut]; exact dif_pos rfl]
        simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
          Option.getD_some, Bool.cond_true]
        rw [update_stkLeftOut_left]
        rw [show stkLeftOut M₂ Mgt₂ ls ys CombK.tmp = ys from rfl]
        rw [update_stkLeftOut_tmp]
      have h2 := EvalsToInTime.trans _ 1 (ls.length + 1) _ _ _ (step_one h1)
        (ih (M₂.outputAlphabet a :: ys))
      simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append,
        Nat.add_comm 1 (ls.length + 1)] using h2

def eval_drainRev_false (rs : List (Mgt₂.tm.Γ Mgt₂.tm.k₁)) (ys : List Bool) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some (.drainRev false)) (s₀ M₂ Mgt₂) (stkRightOut M₂ Mgt₂ rs ys))
      (some (combCfg M₂ Mgt₂ (some .drainOut) (s₀ M₂ Mgt₂)
        (stkOut M₂ Mgt₂ (rs.reverse.map Mgt₂.outputAlphabet ++ ys) [])))
      (rs.length + 1) := by
  induction rs generalizing ys with
  | nil =>
      refine step_one ?_
      dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
      rw [show stkRightOut M₂ Mgt₂ [] ys (CombK.right Mgt₂.tm.k₁) = [] from by
        dsimp only [stkRightOut]; exact dif_pos rfl]
      simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
        Bool.cond_false, List.reverse_nil, List.map_nil, List.nil_append]
      rw [update_stkRightOut_right]
      congr 2; funext k
      cases k with
      | right k' =>
          rcases eq_or_ne k' Mgt₂.tm.k₁ with rfl | hk
          · dsimp only [stkRightOut, stkOut]; exact dif_pos rfl
          · dsimp only [stkRightOut, stkOut]; exact dif_neg hk
      | _ => rfl
  | cons a rs ih =>
      have h1 : (combTM M₂ Mgt₂).step
          (combCfg M₂ Mgt₂ (some (.drainRev false)) (s₀ M₂ Mgt₂) (stkRightOut M₂ Mgt₂ (a :: rs) ys)) =
          some (combCfg M₂ Mgt₂ (some (.drainRev false)) (s₀ M₂ Mgt₂)
            (stkRightOut M₂ Mgt₂ rs (Mgt₂.outputAlphabet a :: ys))) := by
        dsimp only [FinTM2.step, FinTM2.Cfg, TM2.step, combCfg, combTM, combCode, TM2.stepAux]
        rw [show stkRightOut M₂ Mgt₂ (a :: rs) ys (CombK.right Mgt₂.tm.k₁) = a :: rs from by
          dsimp only [stkRightOut]; exact dif_pos rfl]
        simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
          Option.getD_some, Bool.cond_true]
        rw [update_stkRightOut_right]
        rw [show stkRightOut M₂ Mgt₂ rs ys CombK.tmp = ys from rfl]
        rw [update_stkRightOut_tmp]
      have h2 := EvalsToInTime.trans _ 1 (rs.length + 1) _ _ _ (step_one h1)
        (ih (Mgt₂.outputAlphabet a :: ys))
      simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append,
        Nat.add_comm 1 (rs.length + 1)] using h2

def eval_drainOut (ys zs : List Bool) :
    EvalsToInTime (combTM M₂ Mgt₂).step
      (combCfg M₂ Mgt₂ (some .drainOut) (s₀ M₂ Mgt₂) (stkOut M₂ Mgt₂ ys zs))
      (some (haltList (combTM M₂ Mgt₂) (ys.reverse ++ zs)))
      (ys.length + 1) := by
  induction ys generalizing zs with
  | nil =>
      refine step_one ?_
      change some (combCfg M₂ Mgt₂ none (s₀ M₂ Mgt₂)
        (Function.update (stkOut M₂ Mgt₂ [] zs) .tmp [])) = _
      rw [update_stkOut_tmp]
      congr 1
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | out =>
          dsimp only [combCfg, haltList, stkOut]
          rw [dif_pos rfl]
          rfl
      | _ =>
          dsimp only [combCfg, haltList, stkOut]
          rw [dif_neg (by intro h; cases h)]
  | cons b ys ih =>
      have h1 : (combTM M₂ Mgt₂).step
          (combCfg M₂ Mgt₂ (some .drainOut) (s₀ M₂ Mgt₂) (stkOut M₂ Mgt₂ (b :: ys) zs)) =
          some (combCfg M₂ Mgt₂ (some .drainOut) (s₀ M₂ Mgt₂) (stkOut M₂ Mgt₂ ys (b :: zs))) := by
        change some (combCfg M₂ Mgt₂ (some .drainOut) (s₀ M₂ Mgt₂)
          (Function.update (Function.update (stkOut M₂ Mgt₂ (b :: ys) zs) .tmp ys) .out
            (b :: zs))) = _
        rw [update_stkOut_tmp, update_stkOut_out]
      have h2 := EvalsToInTime.trans _ 1 (ys.length + 1) _ _ _ (step_one h1) (ih (b :: zs))
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        Nat.add_comm 1 (ys.length + 1)] using h2

end Build

noncomputable def combTime {f₂ fgt₂ : Str → Str}
    (M₂ : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f₂)
    (Mgt₂ : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) fgt₂) : Polynomial ℕ :=
  4 * Polynomial.X + Polynomial.C 4 +
    (1 + 2 * Polynomial.C (tmGrowth M₂.tm)) * M₂.time +
    (1 + 2 * Polynomial.C (tmGrowth Mgt₂.tm)) * Mgt₂.time

lemma comb_polytime {f₂ fgt₂ : Str → Str}
    (M₂ : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f₂)
    (Mgt₂ : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) fgt₂) :
    PolyTimeComputable (fun s : Str => if isQ2Prefix s then f₂ s else fgt₂ s) := by
  refine ⟨{
    tm := combTM M₂ Mgt₂
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := combTime M₂ Mgt₂
    outputsFun := fun s => ?_
  }⟩
  dsimp only [Equiv.refl]
  simp only [id_eq, List.map_id]
  have hinit : initList (combTM M₂ Mgt₂) s =
      combCfg M₂ Mgt₂ (some (.scan 0)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ s []) := by
    refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
    cases k with
    | inp => dsimp only [initList, combCfg, stkInpTmp]; exact dif_pos rfl
    | _ => dsimp only [initList, combCfg, stkInpTmp]; exact dif_neg (by intro h; cases h)
  have hscan := eval_scan M₂ Mgt₂ 0 s [] rfl rfl
  rw [List.reverse_nil, List.nil_append, List.append_nil, ← hinit] at hscan
  by_cases hq : isQ2Prefix s = true
  · rw [hq] at hscan
    rw [if_pos hq]
    have hpush := eval_push_true M₂ Mgt₂ s.reverse []
    have hpush_cfg1 : combCfg M₂ Mgt₂ (some (.push true)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ [] s.reverse) =
        combCfg M₂ Mgt₂ (some (.push true)) (s₀ M₂ Mgt₂) (stkTmpLeft M₂ Mgt₂ s.reverse []) := by
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | left k' =>
          dsimp only [combCfg, stkInpTmp, stkTmpLeft]
          rcases eq_or_ne k' M₂.tm.k₀ with rfl | hk
          · rw [dif_pos rfl]
          · simp only [dif_neg hk]
      | _ => rfl
    have hpush_cfg2 : combCfg M₂ Mgt₂ (some (.runLeft M₂.tm.main)) (s₀ M₂ Mgt₂)
          (stkTmpLeft M₂ Mgt₂ [] (s.reverse.reverse.map M₂.inputAlphabet.symm ++ [])) =
        leftCfg M₂ Mgt₂ (initList M₂.tm (s.map M₂.inputAlphabet.symm)) := by
      rw [List.reverse_reverse, List.append_nil]
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | left k' =>
          dsimp only [combCfg, stkTmpLeft, leftCfg, stkLeft, initList]
          rcases eq_or_ne k' M₂.tm.k₀ with rfl | hk
          · rw [dif_pos rfl]; rw [dif_pos rfl]; try rfl
          · simp only [dif_neg hk]
      | _ => rfl
    rw [← hpush_cfg1] at hpush
    rw [hpush_cfg2] at hpush
    have hout2 := M₂.outputsFun s
    simp only [id_eq] at hout2
    have hsim : EvalsToInTime (combTM M₂ Mgt₂).step
        (leftCfg M₂ Mgt₂ (initList M₂.tm (s.map M₂.inputAlphabet.symm)))
        (some (leftCfg M₂ Mgt₂ (haltList M₂.tm ((f₂ s).map M₂.outputAlphabet.symm))))
        (M₂.time.eval s.length) :=
      ⟨⟨hout2.steps, sim_left M₂ Mgt₂ hout2.steps _ _ hout2.evals_in_steps⟩, hout2.steps_le_m⟩
    have hdrain_cfg1 : leftCfg M₂ Mgt₂ (haltList M₂.tm ((f₂ s).map M₂.outputAlphabet.symm)) =
        combCfg M₂ Mgt₂ (some (.drainRev true)) (s₀ M₂ Mgt₂)
          (stkLeftOut M₂ Mgt₂ ((f₂ s).map M₂.outputAlphabet.symm) []) := by
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | left k' =>
          dsimp only [combCfg, leftCfg, stkLeft, haltList, stkLeftOut]
          rcases eq_or_ne k' M₂.tm.k₁ with rfl | hk
          · rw [dif_pos rfl]; rw [dif_pos rfl]; try rfl
          · simp only [dif_neg hk]
      | _ => rfl
    have hdrain1 := eval_drainRev_true M₂ Mgt₂ ((f₂ s).map M₂.outputAlphabet.symm) []
    rw [← hdrain_cfg1, List.append_nil, List.map_reverse, List.map_map] at hdrain1
    have hmapid : (⇑M₂.outputAlphabet ∘ ⇑M₂.outputAlphabet.symm) = id := by
      funext x; simp
    rw [hmapid, List.map_id, List.length_map] at hdrain1
    have hdrain2 := eval_drainOut M₂ Mgt₂ (f₂ s).reverse []
    rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hdrain2
    have hc1 := EvalsToInTime.trans _ _ _ _ _ _ hscan hpush
    have hc2 := EvalsToInTime.trans _ _ _ _ _ _ hc1 hsim
    have hc3 := EvalsToInTime.trans _ _ _ _ _ _ hc2 hdrain1
    have hc4 := EvalsToInTime.trans _ _ _ _ _ _ hc3 hdrain2
    refine ⟨hc4.toEvalsTo, hc4.steps_le_m.trans ?_⟩
    have hlen2 := tm2_output_length M₂ s
    simp only [combTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, List.length_reverse]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm (tmGrowth M₂.tm)]
    omega
  · have hqf : isQ2Prefix s = false := Bool.eq_false_iff.mpr hq
    rw [hqf] at hscan
    rw [if_neg hq]
    have hpush := eval_push_false M₂ Mgt₂ s.reverse []
    have hpush_cfg1 : combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂) (stkInpTmp M₂ Mgt₂ [] s.reverse) =
        combCfg M₂ Mgt₂ (some (.push false)) (s₀ M₂ Mgt₂) (stkTmpRight M₂ Mgt₂ s.reverse []) := by
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | right k' =>
          dsimp only [combCfg, stkInpTmp, stkTmpRight]
          rcases eq_or_ne k' Mgt₂.tm.k₀ with rfl | hk
          · rw [dif_pos rfl]
          · simp only [dif_neg hk]
      | _ => rfl
    have hpush_cfg2 : combCfg M₂ Mgt₂ (some (.runRight Mgt₂.tm.main)) (s₀ M₂ Mgt₂)
          (stkTmpRight M₂ Mgt₂ [] (s.reverse.reverse.map Mgt₂.inputAlphabet.symm ++ [])) =
        rightCfg M₂ Mgt₂ (initList Mgt₂.tm (s.map Mgt₂.inputAlphabet.symm)) := by
      rw [List.reverse_reverse, List.append_nil]
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | right k' =>
          dsimp only [combCfg, stkTmpRight, rightCfg, stkRight, initList]
          rcases eq_or_ne k' Mgt₂.tm.k₀ with rfl | hk
          · rw [dif_pos rfl]; rw [dif_pos rfl]; try rfl
          · simp only [dif_neg hk]
      | _ => rfl
    rw [← hpush_cfg1] at hpush
    rw [hpush_cfg2] at hpush
    have houtgt2 := Mgt₂.outputsFun s
    simp only [id_eq] at houtgt2
    have hsim : EvalsToInTime (combTM M₂ Mgt₂).step
        (rightCfg M₂ Mgt₂ (initList Mgt₂.tm (s.map Mgt₂.inputAlphabet.symm)))
        (some (rightCfg M₂ Mgt₂ (haltList Mgt₂.tm ((fgt₂ s).map Mgt₂.outputAlphabet.symm))))
        (Mgt₂.time.eval s.length) :=
      ⟨⟨houtgt2.steps, sim_right M₂ Mgt₂ houtgt2.steps _ _ houtgt2.evals_in_steps⟩, houtgt2.steps_le_m⟩
    have hdrain_cfg1 : rightCfg M₂ Mgt₂ (haltList Mgt₂.tm ((fgt₂ s).map Mgt₂.outputAlphabet.symm)) =
        combCfg M₂ Mgt₂ (some (.drainRev false)) (s₀ M₂ Mgt₂)
          (stkRightOut M₂ Mgt₂ ((fgt₂ s).map Mgt₂.outputAlphabet.symm) []) := by
      refine combCfg_ext M₂ Mgt₂ rfl rfl fun k => ?_
      cases k with
      | right k' =>
          dsimp only [combCfg, rightCfg, stkRight, haltList, stkRightOut]
          rcases eq_or_ne k' Mgt₂.tm.k₁ with rfl | hk
          · rw [dif_pos rfl]; rw [dif_pos rfl]; try rfl
          · simp only [dif_neg hk]
      | _ => rfl
    have hdrain1 := eval_drainRev_false M₂ Mgt₂ ((fgt₂ s).map Mgt₂.outputAlphabet.symm) []
    rw [← hdrain_cfg1, List.append_nil, List.map_reverse, List.map_map] at hdrain1
    have hmapid : (⇑Mgt₂.outputAlphabet ∘ ⇑Mgt₂.outputAlphabet.symm) = id := by
      funext x; simp
    rw [hmapid, List.map_id, List.length_map] at hdrain1
    have hdrain2 := eval_drainOut M₂ Mgt₂ (fgt₂ s).reverse []
    rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hdrain2
    have hc1 := EvalsToInTime.trans _ _ _ _ _ _ hscan hpush
    have hc2 := EvalsToInTime.trans _ _ _ _ _ _ hc1 hsim
    have hc3 := EvalsToInTime.trans _ _ _ _ _ _ hc2 hdrain1
    have hc4 := EvalsToInTime.trans _ _ _ _ _ _ hc3 hdrain2
    refine ⟨hc4.toEvalsTo, hc4.steps_le_m.trans ?_⟩
    have hlengt2 := tm2_output_length Mgt₂ s
    simp only [combTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, List.length_reverse]
    have he : (1 + 2 * tmGrowth Mgt₂.tm) * Mgt₂.time.eval s.length =
        Mgt₂.time.eval s.length + 2 * (Mgt₂.time.eval s.length * tmGrowth Mgt₂.tm) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm (tmGrowth Mgt₂.tm)]
    rw [he]
    omega

end CombinedTM

def castCirc {m n : ℕ} (h : m = n) (c : List (QAlgorithms.Complexity.Instr m)) :
    List (QAlgorithms.Complexity.Instr n) :=
  h ▸ c

lemma castCirc_length {m n : ℕ} (h : m = n) (c : List (QAlgorithms.Complexity.Instr m)) :
    (castCirc h c).length = c.length := by
  subst h; rfl

lemma encLayer_castCirc {m n : ℕ} (h : m = n) (c : List (QAlgorithms.Complexity.Instr m)) :
    QAlgorithms.Complexity.encLayer (castCirc h c) = QAlgorithms.Complexity.encLayer c := by
  subst h; rfl

lemma castCirc_implements {X Y : Type} [Fintype X] [Fintype Y] {inW outW m n : ℕ}
    (h : m = n) (c : List (QAlgorithms.Complexity.Instr m))
    (cin : X → QAlgorithms.Qubits inW) (cout : Y → QAlgorithms.Qubits outW)
    (Φ : Matrix Y X ℂ) (ε : ℝ)
    (himpl : Implements (circUnitary c) (fun x => padTo m (cin x))
      (fun y => padTo m (cout y)) Φ ε) :
    Implements (circUnitary (castCirc h c)) (fun x => padTo n (cin x))
      (fun y => padTo n (cout y)) Φ ε := by
  subst h; exact himpl

end GL2QFT_ByQ2_Aux

theorem solution {P : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)]
    [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)}
    {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h2 : UniformlyImplementsOn (fun D => P D ∧ D.q = 2) cin cout Φ)
    (hgt2 : UniformlyImplementsOn (fun D => P D ∧ 2 < D.q) cin cout Φ) :
    UniformlyImplementsOn P cin cout Φ := by
  rcases h2 with ⟨wires₂, circ₂, f₂, c₂, ⟨M₂⟩, henc₂, hlen₂, himpl₂⟩
  rcases hgt2 with ⟨wiresgt₂, circgt₂, fgt₂, cgt₂, ⟨Mgt₂⟩, hencgt₂, hlengt₂, himplgt₂⟩
  let wires : FieldData → ℕ → ℕ := fun D k => if D.q = 2 then wires₂ D k else wiresgt₂ D k
  let circ : ∀ D k, List (Instr (wires D k)) := fun D k =>
    if h : D.q = 2 then
      GL2QFT_ByQ2_Aux.castCirc (if_pos h).symm (circ₂ D k)
    else
      GL2QFT_ByQ2_Aux.castCirc (if_neg h).symm (circgt₂ D k)
  let f : Str → Str := fun s => if GL2QFT_ByQ2_Aux.isQ2Prefix s then f₂ s else fgt₂ s
  refine ⟨wires, circ, f, max c₂ cgt₂, GL2QFT_ByQ2_Aux.comb_polytime M₂ Mgt₂, ?_, ?_, ?_⟩
  · intro D hD k
    by_cases hq : D.q = 2
    · have hpre : GL2QFT_ByQ2_Aux.isQ2Prefix (D.encData ++ encNat k) = true :=
        (GL2QFT_ByQ2_Aux.isQ2Prefix_encData D k).mpr hq
      simp only [f, wires, circ, if_pos hpre, dif_pos hq, if_pos hq,
        GL2QFT_ByQ2_Aux.encLayer_castCirc]
      exact henc₂ D ⟨hD, hq⟩ k
    · have hgt : 2 < D.q := by have := D.one_lt_q; omega
      have hpre : GL2QFT_ByQ2_Aux.isQ2Prefix (D.encData ++ encNat k) = false :=
        Bool.eq_false_iff.mpr fun h => hq ((GL2QFT_ByQ2_Aux.isQ2Prefix_encData D k).mp h)
      simp only [f, wires, circ, hpre, Bool.false_eq_true, ↓reduceIte, dif_neg hq, if_neg hq,
        GL2QFT_ByQ2_Aux.encLayer_castCirc]
      exact hencgt₂ D ⟨hD, hgt⟩ k
  · intro D hD k
    by_cases hq : D.q = 2
    · simp only [circ, dif_pos hq, GL2QFT_ByQ2_Aux.castCirc_length]
      have h1 := hlen₂ D ⟨hD, hq⟩ k
      have hb : 1 ≤ Nat.log 2 D.q + k + 2 := by omega
      exact h1.trans (Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right hb (le_max_left _ _)))
    · have hgt : 2 < D.q := by have := D.one_lt_q; omega
      simp only [circ, dif_neg hq, GL2QFT_ByQ2_Aux.castCirc_length]
      have h1 := hlengt₂ D ⟨hD, hgt⟩ k
      have hb : 1 ≤ Nat.log 2 D.q + k + 2 := by omega
      exact h1.trans (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right hb (le_max_right _ _)))
  · intro D hD k
    by_cases hq : D.q = 2
    · obtain ⟨hin, hout, him⟩ := himpl₂ D ⟨hD, hq⟩ k
      simp only [wires, circ, if_pos hq, dif_pos hq]
      exact ⟨hin, hout, GL2QFT_ByQ2_Aux.castCirc_implements (if_pos hq).symm (circ₂ D k) _ _ _ _ him⟩
    · have hgt : 2 < D.q := by have := D.one_lt_q; omega
      obtain ⟨hin, hout, him⟩ := himplgt₂ D ⟨hD, hgt⟩ k
      simp only [wires, circ, if_neg hq, dif_neg hq]
      exact ⟨hin, hout,
        GL2QFT_ByQ2_Aux.castCirc_implements (if_neg hq).symm (circgt₂ D k) _ _ _ _ him⟩
