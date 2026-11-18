-- Prove2me | solution 1 for CritWinSpin.p4c_1_1_ii_effpoly
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-17T07:46:17.923272+00:00
-- url     : https://prove2.me/submissions/e6377170-bb66-4b24-b075-8f9a60d23614

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily

open CookPvsNP QuantumPRC
set_option autoImplicit false

namespace CritWinSpin

section TMHelpers

lemma p4c11e_run_zero {Γ : Type} (M : TM Γ) (c : Cfg Γ M.Q) : M.run 0 c = c := rfl

lemma p4c11e_run_succ {Γ : Type} (M : TM Γ) (n : ℕ) (c : Cfg Γ M.Q) :
    M.run (n + 1) c = M.run n (M.step c) := by
  simp only [TM.run, Function.iterate_succ, Function.comp_apply]

lemma p4c11e_run_add {Γ : Type} (M : TM Γ) (m n : ℕ) (c : Cfg Γ M.Q) :
    M.run (m + n) c = M.run n (M.run m c) := by
  simp only [TM.run, Nat.add_comm m n, Function.iterate_add_apply]

lemma p4c11e_run_halting {Γ : Type} (M : TM Γ) (n : ℕ) (c : Cfg Γ M.Q) (hc : M.IsHalting c) :
    M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [TM.run, Function.iterate_succ', Function.comp_apply]
    change M.step (M.run n c) = c
    rw [ih]
    unfold TM.step
    simp [hc]

lemma p4c11e_halts_mono {Γ : Type} (M : TM Γ) {n m : ℕ} (w : List Γ) (hnm : n ≤ m)
    (h : M.HaltsWithin n w) : M.HaltsWithin m w := by
  unfold TM.HaltsWithin at h ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [p4c11e_run_add, p4c11e_run_halting M k _ h]
  exact h

lemma p4c11e_run_mono_output {Γ : Type} (M : TM Γ) {n m : ℕ} (w : List Γ) (hnm : n ≤ m)
    (h : M.HaltsWithin n w) :
    M.run m (M.init w) = M.run n (M.init w) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [p4c11e_run_add, p4c11e_run_halting M k _ h]

lemma p4c11e_step_right {Γ : Type} (M : TM Γ) (q q' : M.Q) (hq : q ≠ M.qaccept ∧ q ≠ M.qreject)
    (L R : List (Option Γ)) (h v : Option Γ)
    (hδ : M.δ q h = (q', v, Move.right)) :
    M.step { state := q, left := L, head := h, right := R } =
      { state := q', left := v :: L, head := R.headD none, right := R.tail } := by
  unfold TM.step TM.IsHalting
  simp [hq.1, hq.2, hδ]

lemma p4c11e_step_left {Γ : Type} (M : TM Γ) (q q' : M.Q) (hq : q ≠ M.qaccept ∧ q ≠ M.qreject)
    (u : Option Γ) (L R : List (Option Γ)) (h v : Option Γ)
    (hδ : M.δ q h = (q', v, Move.left)) :
    M.step { state := q, left := u :: L, head := h, right := R } =
      { state := q', left := L, head := u, right := v :: R } := by
  unfold TM.step TM.IsHalting
  simp [hq.1, hq.2, hδ]

lemma p4c11e_scanRight {Γ : Type} (M : TM Γ) (q : M.Q) (hq : q ≠ M.qaccept ∧ q ≠ M.qreject)
    (f : Option Γ → Option Γ) (A : List (Option Γ))
    (hstep : ∀ x ∈ A, M.δ q x = (q, f x, Move.right))
    (L R : List (Option Γ)) :
    M.run A.length { state := q, left := L, head := (A ++ R).headD none, right := (A ++ R).tail } =
      { state := q, left := (A.map f).reverse ++ L, head := R.headD none, right := R.tail } := by
  induction A generalizing L with
  | nil => simp [p4c11e_run_zero]
  | cons a A ih =>
    simp only [List.length_cons, List.cons_append, List.headD_cons, List.tail_cons, List.map_cons,
      List.reverse_cons]
    rw [p4c11e_run_succ, p4c11e_step_right M q q hq L (A ++ R) a (f a) (hstep a (by simp))]
    rw [ih (fun x hx => hstep x (by simp [hx])) (f a :: L)]
    simp [List.append_assoc]

lemma p4c11e_scanLeft {Γ : Type} (M : TM Γ) (q : M.Q) (hq : q ≠ M.qaccept ∧ q ≠ M.qreject)
    (f : Option Γ → Option Γ) (A : List (Option Γ)) (v b : Option Γ)
    (hv : M.δ q v = (q, f v, Move.left))
    (hstep : ∀ x ∈ A, M.δ q x = (q, f x, Move.left))
    (L R : List (Option Γ)) :
    M.run (A.length + 1) { state := q, left := A ++ (b :: L), head := v, right := R } =
      { state := q, left := L, head := b, right := (A.map f).reverse ++ [f v] ++ R } := by
  induction A generalizing v R with
  | nil =>
    simp only [List.length_nil, zero_add, List.nil_append, List.map_nil, List.reverse_nil]
    rw [p4c11e_run_succ, p4c11e_step_left M q q hq b L R v (f v) hv]
    rfl
  | cons a A ih =>
    simp only [List.length_cons, List.cons_append, List.map_cons, List.reverse_cons]
    rw [p4c11e_run_succ, p4c11e_step_left M q q hq a (A ++ b :: L) R v (f v) hv]
    rw [ih a (hstep a (by simp)) (fun x hx => hstep x (List.mem_cons_of_mem a hx)) (f v :: R)]
    simp [List.append_assoc]

lemma p4c11e_output_some {Γ Γ₀ : Type} (M : TM Γ) (ι₂ : Γ₀ ↪ Γ) (q : M.Q) (L : List (Option Γ))
    (B : List Γ₀) :
    let cfg : Cfg Γ M.Q :=
      { state := q, left := L,
        head := (B.map (some ∘ ι₂)).headD none,
        right := (B.map (some ∘ ι₂)).tail }
    M.output cfg = B.map (some ∘ ι₂) := by
  cases B with
  | nil => simp [TM.output]
  | cons b B =>
    simp only [TM.output, List.map_cons, List.headD_cons, List.tail_cons]
    have hnone : ∀ x ∈ (b :: B).map (some ∘ ι₂), (Option.isNone x) = false := by
      intro x hx
      simp only [List.mem_map, Function.comp_apply] at hx
      rcases hx with ⟨y, _, rfl⟩
      rfl
    have hdrop : ((List.map (some ∘ ι₂) (b :: B)).reverse.dropWhile Option.isNone) =
        (List.map (some ∘ ι₂) (b :: B)).reverse := by
      cases hrev : (List.map (some ∘ ι₂) (b :: B)).reverse with
      | nil => rfl
      | cons hd tl =>
        have hmem : hd ∈ List.map (some ∘ ι₂) (b :: B) := by
          rw [← List.mem_reverse, hrev]; simp
        simp [hnone hd hmem]
    rw [show ((some ∘ ι₂) b :: List.map (some ∘ ι₂) B) = List.map (some ∘ ι₂) (b :: B) by rfl,
      hdrop, List.reverse_reverse]

lemma p4c11e_dropWhile_isNone_append {Γ : Type} (xs ys : List (Option Γ))
    (hxs : ∀ z ∈ xs, z.isNone = true)
    (hys : ∀ y ys', ys = y :: ys' → y.isNone = false) :
    (xs ++ ys).dropWhile Option.isNone = ys := by
  induction xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys' => simp [hys y ys' rfl]
  | cons x xs ih =>
    simp only [List.cons_append, List.dropWhile_cons, hxs x (by simp), ↓reduceIte]
    exact ih fun z hz => hxs z (by simp [hz])

lemma p4c11e_output_with_blanks {Γ Γ₀ : Type} (M : TM Γ) (ι₂ : Γ₀ ↪ Γ) (q : M.Q)
    (L : List (Option Γ)) (B : List Γ₀) (blanks : List (Option Γ))
    (hblanks : ∀ z ∈ blanks, z = none) :
    let full := B.map (some ∘ ι₂) ++ blanks
    let cfg : Cfg Γ M.Q :=
      { state := q, left := L, head := full.headD none, right := full.tail }
    M.output cfg = B.map (some ∘ ι₂) := by
  cases B with
  | nil =>
    cases blanks with
    | nil => simp [TM.output]
    | cons z zs =>
      have hz : z = none := hblanks z (by simp)
      subst hz
      simp only [List.map_nil, List.nil_append, List.headD_cons, List.tail_cons, TM.output]
      have hnone : ∀ w ∈ (none :: zs).reverse, w.isNone = true := by
        intro w hw
        rw [List.mem_reverse] at hw
        rcases List.mem_cons.mp hw with rfl | hmem
        · rfl
        · rw [hblanks w (by simp [hmem])]; rfl
      rw [← List.append_nil (none :: zs).reverse,
        p4c11e_dropWhile_isNone_append _ [] hnone (fun _ _ h => by simp at h)]
      rfl
  | cons b B' =>
    simp only [List.map_cons, Function.comp_apply, List.cons_append, List.headD_cons, List.tail_cons,
      TM.output, List.reverse_cons, List.reverse_append]
    have hnone_blanks : ∀ w ∈ blanks.reverse, w.isNone = true := by
      intro w hw
      rw [List.mem_reverse] at hw
      rw [hblanks w hw]; rfl
    have hhead : ∀ y ys',
        (B'.map (some ∘ ι₂)).reverse ++ [some (ι₂ b)] = y :: ys' → y.isNone = false := by
      intro y ys' h
      have hy : y ∈ (B'.map (some ∘ ι₂)).reverse ++ [some (ι₂ b)] := by rw [h]; simp
      simp only [List.mem_append, List.mem_reverse, List.mem_map, Function.comp_apply,
        List.mem_singleton] at hy
      rcases hy with ⟨_, _, rfl⟩ | rfl <;> rfl
    rw [List.append_assoc, p4c11e_dropWhile_isNone_append _ _ hnone_blanks hhead,
      ← List.reverse_cons, List.reverse_reverse]

end TMHelpers

section ConstTM

inductive p4c11e_ConstQ (m : ℕ)
  | scan
  | write (k : Fin m)
  | back (k : Fin m)
  | accept
  | reject
  deriving Fintype, DecidableEq

def p4c11e_constTM (m : ℕ) : TM Bool where
  Q := p4c11e_ConstQ m
  q₀ := .scan
  qaccept := .accept
  qreject := .reject
  accept_ne_reject := by intro h; cases h
  δ q s := match q with
    | .scan => match s with
      | some _ => (.scan, some false, .right)
      | none => if hm : 0 < m then (.write ⟨0, hm⟩, some false, .right) else (.accept, none, .right)
    | .write k =>
      if hk : k.1 + 1 < m then (.write ⟨k.1 + 1, hk⟩, some true, .right)
      else (.back k, some true, .right)
    | .back k =>
      if hk : k.1 = 0 then (.accept, s, .left)
      else (.back ⟨k.1 - 1, by omega⟩, s, .left)
    | .accept => (.accept, s, .right)
    | .reject => (.reject, s, .right)

lemma p4c11e_constTM_spec (m : ℕ) : PolyTimeComputable (fun _x : List Bool => unary m) := by
  refine ⟨Bool, inferInstance, Function.Embedding.refl Bool, Function.Embedding.refl Bool,
    p4c11e_constTM m, 2 * m + 10, ?_⟩
  intro x
  have hscan : (p4c11e_constTM m).run x.length ((p4c11e_constTM m).init x) =
      { state := .scan, left := List.replicate x.length (some false), head := none, right := [] } := by
    have h0 := p4c11e_scanRight (p4c11e_constTM m) .scan
      ⟨(by dsimp [p4c11e_constTM]; intro h; cases h),
       (by dsimp [p4c11e_constTM]; intro h; cases h)⟩
      (fun _ => some false) (x.map some)
      (fun s hs => by
        simp only [List.mem_map] at hs
        rcases hs with ⟨b, _, rfl⟩
        rfl) [] []
    dsimp only [TM.init]
    have hq0 : (p4c11e_constTM m).q₀ = .scan := rfl
    rw [hq0]
    simpa [Function.comp_def, List.map_const', List.reverse_replicate] using h0
  by_cases hm : 0 < m
  · have hwrite : ∀ (j : ℕ) (hj : j ≤ m) (L : List (Option Bool)),
          (p4c11e_constTM m).run (m - j)
            { state := if h : j < m then .write ⟨j, h⟩ else .back ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩,
              left := L, head := none, right := [] } =
            { state := .back ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩,
              left := List.replicate (m - j) (some true) ++ L, head := none, right := [] } := by
        intro j hj L
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
        have hdm : m - j = d := by omega
        rw [hdm]
        clear hdm
        induction d generalizing j L with
        | zero =>
          have hjm : j = m := by omega
          subst hjm
          simp [p4c11e_run_zero]
        | succ d ih =>
          have hlt : j < m := by omega
          dsimp only [p4c11e_constTM] at ih ⊢
          simp only [dif_pos hlt]
          rw [p4c11e_run_succ]
          have hstep : (p4c11e_constTM m).step
              { state := .write ⟨j, hlt⟩, left := L, head := none, right := [] } =
              { state := if h' : j + 1 < m then .write ⟨j + 1, h'⟩
                  else .back ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩,
                left := some true :: L, head := none, right := [] } := by
            unfold TM.step TM.IsHalting p4c11e_constTM
            dsimp only
            by_cases hk : j + 1 < m
            · simp [hk]
            · have hje : j = m - 1 := by omega
              simp only [dif_neg hk]
              simp [hje]
          dsimp only [p4c11e_constTM] at hstep
          rw [hstep]
          have ih' := ih (j + 1) (by omega) (some true :: L) (by omega)
          rw [ih']
          simp [List.replicate_succ']
    have hback : ∀ (k : ℕ) (hk : k < m) (L R : List (Option Bool)) (h0 : Option Bool),
        (p4c11e_constTM m).run (k + 1)
          { state := .back ⟨k, hk⟩, left := List.replicate (k + 1) (some true) ++ L,
            head := h0, right := R } =
          { state := .accept, left := L, head := some true,
            right := List.replicate k (some true) ++ (h0 :: R) } := by
      intro k
      induction k with
      | zero =>
        intro hk L R h0
        simp only [Nat.zero_add, List.replicate_one, List.singleton_append, List.replicate_zero,
          List.nil_append]
        rw [p4c11e_run_succ]
        unfold TM.step TM.IsHalting p4c11e_constTM
        simp [p4c11e_run_zero]
      | succ k ih =>
        intro hk L R h0
        rw [p4c11e_run_succ]
        have hk' : k < m := by omega
        have hstep : (p4c11e_constTM m).step
            { state := .back ⟨k + 1, hk⟩,
              left := List.replicate (k + 2) (some true) ++ L,
              head := h0, right := R } =
            { state := .back ⟨k, hk'⟩,
              left := List.replicate (k + 1) (some true) ++ L,
              head := some true, right := h0 :: R } := by
          unfold TM.step TM.IsHalting p4c11e_constTM
          simp [List.replicate_succ]
        rw [hstep, ih hk' L (h0 :: R) (some true)]
        simp [List.replicate_succ']
    have hnone_step : (p4c11e_constTM m).step
        { state := .scan, left := List.replicate x.length (some false), head := none, right := [] } =
        { state := .write ⟨0, hm⟩, left := some false :: List.replicate x.length (some false),
          head := none, right := [] } := by
      unfold TM.step TM.IsHalting p4c11e_constTM
      simp [hm]
    have hrun_full : (p4c11e_constTM m).run (x.length + 1 + m + m) ((p4c11e_constTM m).init x) =
        { state := .accept, left := some false :: List.replicate x.length (some false),
          head := some true, right := List.replicate (m - 1) (some true) ++ [none] } := by
      have hnone_run : (p4c11e_constTM m).run 1
          { state := .scan, left := List.replicate x.length (some false), head := none, right := [] } =
          { state := .write ⟨0, hm⟩, left := some false :: List.replicate x.length (some false),
            head := none, right := [] } := by
        rw [p4c11e_run_succ, hnone_step, p4c11e_run_zero]
      have hw : (p4c11e_constTM m).run m
          { state := .write ⟨0, hm⟩, left := some false :: List.replicate x.length (some false),
            head := none, right := [] } =
          { state := .back ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩,
            left := List.replicate m (some true) ++ (some false :: List.replicate x.length (some false)),
            head := none, right := [] } := by
        have h := hwrite 0 (Nat.zero_le m) (some false :: List.replicate x.length (some false))
        dsimp only [p4c11e_constTM] at h ⊢
        simp only [Nat.sub_zero, dif_pos hm] at h
        exact h
      rw [p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, hscan, hnone_run, hw]
      have hm1 : m - 1 + 1 = m := by omega
      have hrepl : List.replicate m (some true) =
          List.replicate ((m - 1) + 1) (some true) := by congr 1; omega
      have hb := hback (m - 1) (Nat.sub_lt hm Nat.one_pos)
        (some false :: List.replicate x.length (some false)) [] none
      simpa [hm1, hrepl] using hb
    have hhalt : (p4c11e_constTM m).HaltsWithin (x.length + 1 + m + m) x := by
      unfold TM.HaltsWithin TM.IsHalting
      rw [hrun_full]; left; rfl
    have hle : x.length + 1 + m + m ≤ x.length ^ (2 * m + 10) + (2 * m + 10) := by
      have hpow : x.length ≤ x.length ^ (2 * m + 10) :=
        Nat.le_self_pow (by omega) x.length
      omega
    have hid : (Function.Embedding.refl Bool : Bool → Bool) = id := rfl
    refine ⟨?_, ?_⟩
    · simpa [hid, List.map_id] using p4c11e_halts_mono _ x hle hhalt
    · simp only [hid, List.map_id, Function.comp_id]
      rw [p4c11e_run_mono_output _ x hle hhalt, hrun_full]
      have hunary_pos : unary m = true :: List.replicate (m - 1) true := by
        unfold unary
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        rw [List.replicate_succ]
      have hout := p4c11e_output_with_blanks (p4c11e_constTM m) (Function.Embedding.refl Bool)
        .accept (some false :: List.replicate x.length (some false)) (unary m) [none]
        (fun z hz => by simpa using hz)
      have hhead : ((unary m).map (some ∘ Function.Embedding.refl Bool) ++ [none]).headD none =
          some true := by
        rw [hunary_pos]; rfl
      have htail : ((unary m).map (some ∘ Function.Embedding.refl Bool) ++ [none]).tail =
          List.replicate (m - 1) (some true) ++ [none] := by
        rw [hunary_pos]
        simp [List.map_replicate]
      dsimp only at hout
      rw [hhead, htail] at hout
      simpa [hid, Function.comp_id] using hout
  · have hm0 : m = 0 := by omega
    subst hm0
    have hstep : (p4c11e_constTM 0).step
        { state := .scan, left := List.replicate x.length (some false), head := none, right := [] } =
        { state := .accept, left := none :: List.replicate x.length (some false), head := none, right := [] } := by
      unfold TM.step TM.IsHalting p4c11e_constTM
      simp
    have hrun_full : (p4c11e_constTM 0).run (x.length + 1) ((p4c11e_constTM 0).init x) =
        { state := .accept, left := none :: List.replicate x.length (some false),
          head := none, right := [] } := by
      rw [p4c11e_run_add, hscan, p4c11e_run_succ, hstep, p4c11e_run_zero]
    have hhalt : (p4c11e_constTM 0).HaltsWithin (x.length + 1) x := by
      unfold TM.HaltsWithin TM.IsHalting
      rw [hrun_full]; left; rfl
    have hle : x.length + 1 ≤ x.length ^ (2 * 0 + 10) + (2 * 0 + 10) := by
      have hpow : x.length ≤ x.length ^ 10 := Nat.le_self_pow (by omega) x.length
      simpa using (by omega : x.length + 1 ≤ x.length ^ 10 + 10)
    have hid : (Function.Embedding.refl Bool : Bool → Bool) = id := rfl
    refine ⟨?_, ?_⟩
    · simpa [hid, List.map_id] using p4c11e_halts_mono _ x hle hhalt
    · simp only [hid, List.map_id, Function.comp_id]
      rw [p4c11e_run_mono_output _ x hle hhalt, hrun_full]
      simp [TM.output, unary]

end ConstTM

section MulTM

lemma p4c11e_poly_dom (B₀ d n : ℕ) :
    B₀ * n ^ d + B₀ ≤ n ^ (d + 2 * B₀ + 2) + (d + 2 * B₀ + 2) := by
  rcases Nat.lt_trichotomy n 1 with hn0 | hn1 | hn2
  · have hn : n = 0 := by omega
    subst hn
    have h0d : 0 ^ d ≤ 1 := by
      cases d with
      | zero => simp
      | succ d => simp
    have hmul : B₀ * 0 ^ d ≤ B₀ := by
      calc
        B₀ * 0 ^ d ≤ B₀ * 1 := Nat.mul_le_mul_left B₀ h0d
        _ = B₀ := Nat.mul_one B₀
    have h2 : B₀ + B₀ ≤ d + 2 * B₀ + 2 := by omega
    exact le_trans (Nat.add_le_add_right hmul B₀) (le_trans h2 (Nat.le_add_left _ _))
  · subst hn1
    simp only [one_pow, mul_one]
    omega
  · have hn2' : 2 ≤ n := by omega
    have hB₀ : B₀ ≤ n ^ B₀ := by
      calc
        B₀ ≤ 2 ^ B₀ := Nat.lt_two_pow_self.le
        _ ≤ n ^ B₀ := Nat.pow_le_pow_left hn2' B₀
    have hpow1 : B₀ * n ^ d ≤ n ^ B₀ * n ^ d := Nat.mul_le_mul_right _ hB₀
    have hpow2 : n ^ B₀ * n ^ d ≤ n ^ (d + 2 * B₀ + 2) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega

inductive p4c11e_Sym
  | bit (val : Bool)
  | inFirst
  | inU
  | inDone
  | sep
  | tok
  | tokDone
  | nxt
  deriving Fintype, DecidableEq

def p4c11e_symEmb : Bool ↪ p4c11e_Sym where
  toFun := p4c11e_Sym.bit
  inj' a b h := by cases h; rfl

inductive p4c11e_MulQ (a b c : ℕ)
  | init
  | scanIn
  | writeTok (k : Fin a)
  | findTok (r : Fin b)
  | findTokScan (r : Fin b)
  | seekIn (r : Fin b)
  | emitNxt (r : Fin b)
  | restoreIn (r : Fin b)
  | emitFirst (r : Fin b)
  | promote (r : Fin b)
  | appendC (k : Fin c)
  | finalizeScan
  | accept
  | reject
  deriving Fintype, DecidableEq

def p4c11e_mulTM (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : TM p4c11e_Sym where
  Q := p4c11e_MulQ a b c
  q₀ := .init
  qaccept := .accept
  qreject := .reject
  accept_ne_reject := by intro h; cases h
  δ q s := match q with
    | .init => match s with
      | some (.bit _) => (.scanIn, some .inFirst, .right)
      | none => if hc : 0 < c then (.appendC ⟨0, hc⟩, some .sep, .right) else (.accept, none, .right)
      | some _ => (.reject, s, .right)
    | .scanIn => match s with
      | some (.bit _) => (.scanIn, some .inU, .right)
      | none => (.writeTok ⟨0, ha⟩, some .sep, .right)
      | some _ => (.reject, s, .right)
    | .writeTok k =>
      if hk : k.1 + 1 < a then (.writeTok ⟨k.1 + 1, hk⟩, some .tok, .right)
      else (.findTok ⟨0, hb⟩, some .tok, .right)
    | .findTok r => (.findTokScan r, s, .left)
    | .findTokScan r => match s with
      | some .nxt => (.findTokScan r, some .nxt, .left)
      | some .tokDone => (.findTokScan r, some .tokDone, .left)
      | some .tok => (.seekIn r, some .tokDone, .left)
      | some .sep => (.promote r, some .sep, .right)
      | _ => (.reject, s, .right)
    | .seekIn r => match s with
      | some .inU => (.emitNxt r, some .inDone, .right)
      | some .inFirst => (.restoreIn r, some .inFirst, .right)
      | some .inDone => (.seekIn r, some .inDone, .left)
      | some .sep => (.seekIn r, some .sep, .left)
      | some .tok => (.seekIn r, some .tok, .left)
      | some .tokDone => (.seekIn r, some .tokDone, .left)
      | some .nxt => (.seekIn r, some .nxt, .left)
      | _ => (.reject, s, .right)
    | .emitNxt r => match s with
      | none => (.seekIn r, some .nxt, .left)
      | some _ => (.emitNxt r, s, .right)
    | .restoreIn r => match s with
      | some .inDone => (.restoreIn r, some .inU, .right)
      | some .sep => (.emitFirst r, some .sep, .right)
      | _ => (.reject, s, .right)
    | .emitFirst r => match s with
      | none => (.findTok r, some .nxt, .right)
      | some _ => (.emitFirst r, s, .right)
    | .promote r => match s with
      | some .tokDone => (.promote r, some .sep, .right)
      | some .nxt => (.promote r, some .tok, .right)
      | none =>
        if hr : r.1 + 1 < b then (.findTokScan ⟨r.1 + 1, hr⟩, none, .left)
        else if hc : 0 < c then
          if hc1 : 1 < c then (.appendC ⟨1, hc1⟩, some (.bit true), .right)
          else (.finalizeScan, some (.bit true), .left)
        else (.finalizeScan, none, .left)
      | some _ => (.reject, s, .right)
    | .appendC k =>
      if hk : k.1 + 1 < c then (.appendC ⟨k.1 + 1, hk⟩, some (.bit true), .right)
      else (.finalizeScan, some (.bit true), .left)
    | .finalizeScan => match s with
      | some (.bit true) => (.finalizeScan, some (.bit true), .left)
      | some .tok => (.finalizeScan, some (.bit true), .left)
      | some .sep => (.accept, some .sep, .right)
      | _ => (.reject, s, .right)
    | .accept => (.accept, s, .right)
    | .reject => (.reject, s, .right)

def p4c11e_IsMid (x : Option p4c11e_Sym) : Prop :=
  x = some .inDone ∨ x = some .sep ∨ x = some .tok ∨ x = some .tokDone ∨ x = some .nxt

lemma p4c11e_isMid_ne_none {x : Option p4c11e_Sym} (hx : p4c11e_IsMid x) : x ≠ none := by
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp

lemma p4c11e_mul_scanIn (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (x0 : Bool) (xs : List Bool) :
    (p4c11e_mulTM a b c ha hb).run (xs.length + 2 + a)
      ((p4c11e_mulTM a b c ha hb).init ((x0 :: xs).map p4c11e_symEmb)) =
    { state := .findTok ⟨0, hb⟩,
      left := List.replicate a (some .tok) ++ [some .sep] ++
        List.replicate xs.length (some .inU) ++ [some .inFirst],
      head := none, right := [] } := by
  let M := p4c11e_mulTM a b c ha hb
  have h1 : M.step (M.init ((x0 :: xs).map p4c11e_symEmb)) =
      { state := .scanIn, left := [some .inFirst],
        head := (xs.map (some ∘ p4c11e_symEmb)).headD none,
        right := (xs.map (some ∘ p4c11e_symEmb)).tail } := by
    unfold TM.step TM.IsHalting M p4c11e_mulTM TM.init
    have hx0 : p4c11e_symEmb x0 = p4c11e_Sym.bit x0 := rfl
    simp [List.map_map, hx0]
  have hscan : M.run xs.length
      { state := .scanIn, left := [some .inFirst],
        head := (xs.map (some ∘ p4c11e_symEmb)).headD none,
        right := (xs.map (some ∘ p4c11e_symEmb)).tail } =
      { state := .scanIn,
        left := List.replicate xs.length (some .inU) ++ [some .inFirst],
        head := none, right := [] } := by
    have h0 := p4c11e_scanRight M .scanIn
      ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
       (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩
      (fun _ => some .inU) (xs.map (some ∘ p4c11e_symEmb))
      (fun s hs => by
        simp only [List.mem_map, Function.comp_apply] at hs
        rcases hs with ⟨_, _, rfl⟩
        rfl) [some .inFirst] []
    simpa [List.map_map, Function.comp_def, List.map_const', List.reverse_replicate] using h0
  have hnone : M.step
      { state := .scanIn, left := List.replicate xs.length (some .inU) ++ [some .inFirst],
        head := none, right := [] } =
      { state := .writeTok ⟨0, ha⟩,
        left := some .sep :: List.replicate xs.length (some .inU) ++ [some .inFirst],
        head := none, right := [] } := by
    unfold TM.step TM.IsHalting M p4c11e_mulTM; simp
  have hwt : ∀ (j : ℕ) (hj : j ≤ a) (L : List (Option p4c11e_Sym)),
      M.run (a - j)
        { state := if h : j < a then .writeTok ⟨j, h⟩ else .findTok ⟨0, hb⟩,
          left := L, head := none, right := [] } =
        { state := .findTok ⟨0, hb⟩,
          left := List.replicate (a - j) (some .tok) ++ L,
          head := none, right := [] } := by
    intro j hj L
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    have hdm : a - j = d := by omega
    rw [hdm]; clear hdm
    induction d generalizing j L with
    | zero =>
      have hjm : j = a := by omega
      subst hjm
      simp [p4c11e_run_zero]
    | succ d ih =>
      have hlt : j < a := by omega
      dsimp only [M, p4c11e_mulTM] at ih ⊢
      simp only [dif_pos hlt]
      rw [p4c11e_run_succ]
      have hs : M.step { state := .writeTok ⟨j, hlt⟩, left := L, head := none, right := [] } =
          { state := if h' : j + 1 < a then .writeTok ⟨j + 1, h'⟩ else .findTok ⟨0, hb⟩,
            left := some .tok :: L, head := none, right := [] } := by
        unfold TM.step TM.IsHalting M p4c11e_mulTM
        dsimp only
        by_cases hk : j + 1 < a <;> simp [hk]
      dsimp only [M, p4c11e_mulTM] at hs
      rw [hs, ih (j + 1) (by omega) (some .tok :: L) (by omega)]
      simp [List.replicate_succ']
  have hwt0 := hwt 0 (Nat.zero_le a) (some .sep :: List.replicate xs.length (some .inU) ++ [some .inFirst])
  have hwt0' : M.run a
      { state := .writeTok ⟨0, ha⟩,
        left := some .sep :: List.replicate xs.length (some .inU) ++ [some .inFirst],
        head := none, right := [] } =
      { state := .findTok ⟨0, hb⟩,
        left := List.replicate a (some .tok) ++
          (some .sep :: List.replicate xs.length (some .inU) ++ [some .inFirst]),
        head := none, right := [] } := by
    have h := hwt0
    dsimp only [M, p4c11e_mulTM] at h ⊢
    simp only [Nat.sub_zero, dif_pos (by omega : 0 < a)] at h
    exact h
  have h1_run : M.run 1 (M.init ((x0 :: xs).map p4c11e_symEmb)) =
      { state := .scanIn, left := [some .inFirst],
        head := (xs.map (some ∘ p4c11e_symEmb)).headD none,
        right := (xs.map (some ∘ p4c11e_symEmb)).tail } := by
    rw [p4c11e_run_succ, h1, p4c11e_run_zero]
  have hnone_run : M.run 1
      { state := .scanIn, left := List.replicate xs.length (some .inU) ++ [some .inFirst],
        head := none, right := [] } =
      { state := .writeTok ⟨0, ha⟩,
        left := some .sep :: List.replicate xs.length (some .inU) ++ [some .inFirst],
        head := none, right := [] } := by
    rw [p4c11e_run_succ, hnone, p4c11e_run_zero]
  change M.run (xs.length + 2 + a) _ = _
  rw [show xs.length + 2 + a = (1 + xs.length + 1) + a by omega,
    p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, h1_run, hscan, hnone_run, hwt0']
  simp [List.append_assoc]

lemma p4c11e_seekIn_loop (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (r : Fin b) :
    ∀ (u d : ℕ) (S_rest : List (Option p4c11e_Sym))
      (midL midR : List (Option p4c11e_Sym)) (v : Option p4c11e_Sym)
      (R_blank : List (Option p4c11e_Sym))
      (_hS : ∀ z ∈ S_rest, p4c11e_IsMid z)
      (_hmid : midL ++ [v] ++ midR = List.replicate d (some .inDone) ++ (some .sep :: S_rest))
      (_hblank : R_blank = [] ∨ R_blank = [none]),
    ∃ steps, steps ≤ (u + 1) * (2 * (d + 2 * u + S_rest.length + 1) + 5) ∧
      (p4c11e_mulTM a b c ha hb).run steps
        { state := .seekIn r,
          left := midL.reverse ++ List.replicate u (some .inU) ++ [some .inFirst],
          head := v, right := midR ++ R_blank } =
      { state := .findTok r,
        left := (S_rest ++ List.replicate (u + 1) (some p4c11e_Sym.nxt)).reverse ++
          [some .sep] ++ List.replicate (d + u) (some .inU) ++ [some .inFirst],
        head := none, right := [] } := by
  let M := p4c11e_mulTM a b c ha hb
  intro u
  induction u with
  | zero =>
    intro d S_rest midL midR v R_blank hS hmid hblank
    have hmid_mem : ∀ z ∈ midL ++ [v] ++ midR, p4c11e_IsMid z := by
      rw [hmid]; intro z hz
      simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hz
      rcases hz with ⟨_, rfl⟩ | rfl | hz
      · left; rfl
      · right; left; rfl
      · exact hS z hz
    have hv_mid : p4c11e_IsMid v := hmid_mem v (by simp)
    have hML_mid : ∀ z ∈ midL.reverse, p4c11e_IsMid z := fun z hz =>
      hmid_mem z (by simp [List.mem_reverse.mp hz])
    have hseek_d : ∀ x : Option p4c11e_Sym, p4c11e_IsMid x →
        M.δ (.seekIn r) x = (.seekIn r, x, .left) := by
      intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hL : M.run (midL.reverse.length + 1)
        { state := .seekIn r, left := midL.reverse ++ [some .inFirst], head := v,
          right := midR ++ R_blank } =
        { state := .seekIn r, left := [], head := some .inFirst,
          right := midL ++ [v] ++ midR ++ R_blank } := by
      have h0 := p4c11e_scanLeft M (.seekIn r)
        ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
         (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩ id midL.reverse v
        (some .inFirst) (hseek_d v hv_mid) (fun z hz => hseek_d z (hML_mid z hz)) []
        (midR ++ R_blank)
      simpa [List.append_assoc] using h0
    rw [hmid, List.append_assoc] at hL
    have hstep_first : M.step
        { state := .seekIn r, left := [], head := some .inFirst,
          right := List.replicate d (some .inDone) ++ (some .sep :: S_rest) ++ R_blank } =
        { state := .restoreIn r, left := [some .inFirst],
          head := (List.replicate d (some p4c11e_Sym.inDone) ++
            ((some p4c11e_Sym.sep :: S_rest) ++ R_blank)).headD none,
          right := (List.replicate d (some p4c11e_Sym.inDone) ++
            ((some p4c11e_Sym.sep :: S_rest) ++ R_blank)).tail } := by
      unfold TM.step TM.IsHalting M p4c11e_mulTM
      simp [List.append_assoc]
    have hrest := p4c11e_scanRight M (.restoreIn r)
      ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
       (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩
      (fun _ => some .inU) (List.replicate d (some .inDone))
      (fun z hz => by
        rw [(List.mem_replicate.mp hz).2]; rfl)
      [some .inFirst] ((some .sep :: S_rest) ++ R_blank)
    simp only [List.map_replicate, List.reverse_replicate, List.cons_append, List.headD_cons,
      List.tail_cons] at hrest
    have hstep_sep : M.step
        { state := .restoreIn r,
          left := List.replicate d (some .inU) ++ [some .inFirst],
          head := some .sep, right := S_rest ++ R_blank } =
        { state := .emitFirst r,
          left := some .sep :: List.replicate d (some .inU) ++ [some .inFirst],
          head := (S_rest ++ R_blank).headD none,
          right := (S_rest ++ R_blank).tail } := by
      unfold TM.step TM.IsHalting M p4c11e_mulTM; rfl
    have hemit_scan := p4c11e_scanRight M (.emitFirst r)
      ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
       (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩ id S_rest
      (fun z hz => by
        obtain ⟨sym, hsym⟩ : ∃ s, z = some s := by
          rcases hS z hz with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
        rw [hsym]; rfl)
      (some .sep :: List.replicate d (some .inU) ++ [some .inFirst]) R_blank
    have hRblank_hd : R_blank.headD none = none := by
      rcases hblank with rfl | rfl <;> rfl
    have hRblank_tl : R_blank.tail = [] := by
      rcases hblank with rfl | rfl <;> rfl
    rw [hRblank_hd, hRblank_tl] at hemit_scan
    have hstep_done : M.step
        { state := .emitFirst r,
          left := S_rest.reverse ++ (some .sep :: List.replicate d (some .inU) ++ [some .inFirst]),
          head := none, right := [] } =
        { state := .findTok r,
          left := some .nxt :: (S_rest.reverse ++ (some .sep :: List.replicate d (some .inU) ++ [some .inFirst])),
          head := none, right := [] } := by
      unfold TM.step TM.IsHalting M p4c11e_mulTM; rfl
    have hmid_len : midL.length ≤ d + 1 + S_rest.length := by
      have hlen := congrArg List.length hmid
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at hlen
      omega
    refine ⟨(midL.reverse.length + 1) + 1 + d + 1 + S_rest.length + 1, ?_, ?_⟩
    · simp only [List.length_reverse]; omega
    · simp only [List.map_id] at hemit_scan
      have hL' : M.run (midL.reverse.length + 1)
          { state := .seekIn r, left := midL.reverse ++ [some .inFirst], head := v,
            right := midR ++ R_blank } =
          { state := .seekIn r, left := [], head := some .inFirst,
            right := List.replicate d (some .inDone) ++ (some .sep :: S_rest) ++ R_blank } := by
        simpa [List.append_assoc] using hL
      have hstep_first_run : M.run 1
          { state := .seekIn r, left := [], head := some .inFirst,
            right := List.replicate d (some .inDone) ++ (some .sep :: S_rest) ++ R_blank } =
          { state := .restoreIn r, left := [some .inFirst],
            head := (List.replicate d (some p4c11e_Sym.inDone) ++
              ((some p4c11e_Sym.sep :: S_rest) ++ R_blank)).headD none,
            right := (List.replicate d (some p4c11e_Sym.inDone) ++
              ((some p4c11e_Sym.sep :: S_rest) ++ R_blank)).tail } := by
        rw [p4c11e_run_succ, hstep_first, p4c11e_run_zero]
      have hstep_sep_run : M.run 1
          { state := .restoreIn r,
            left := List.replicate d (some .inU) ++ [some .inFirst],
            head := some .sep, right := S_rest ++ R_blank } =
          { state := .emitFirst r,
            left := some .sep :: List.replicate d (some .inU) ++ [some .inFirst],
            head := (S_rest ++ R_blank).headD none,
            right := (S_rest ++ R_blank).tail } := by
        rw [p4c11e_run_succ, hstep_sep, p4c11e_run_zero]
      have hstep_done_run : M.run 1
          { state := .emitFirst r,
            left := S_rest.reverse ++ (some .sep :: List.replicate d (some .inU) ++ [some .inFirst]),
            head := none, right := [] } =
          { state := .findTok r,
            left := some .nxt :: (S_rest.reverse ++ (some .sep :: List.replicate d (some .inU) ++ [some .inFirst])),
            head := none, right := [] } := by
        rw [p4c11e_run_succ, hstep_done, p4c11e_run_zero]
      simp only [List.length_replicate] at hrest
      simp only [List.cons_append, List.append_assoc] at hL' hstep_first_run
      change M.run ((midL.reverse.length + 1) + 1 + d + 1 + S_rest.length + 1) _ = _
      simp only [List.replicate_zero, List.append_nil]
      rw [p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, p4c11e_run_add,
        hL', hstep_first_run, hrest, hstep_sep_run, hemit_scan, hstep_done_run]
      simp [List.append_assoc]
  | succ u ih =>
    intro d S_rest midL midR v R_blank hS hmid hblank
    have hmid_mem : ∀ z ∈ midL ++ [v] ++ midR, p4c11e_IsMid z := by
      rw [hmid]; intro z hz
      simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hz
      rcases hz with ⟨_, rfl⟩ | rfl | hz
      · left; rfl
      · right; left; rfl
      · exact hS z hz
    have hv_mid : p4c11e_IsMid v := hmid_mem v (by simp)
    have hML_mid : ∀ z ∈ midL.reverse, p4c11e_IsMid z := fun z hz =>
      hmid_mem z (by simp [List.mem_reverse.mp hz])
    have hseek_d : ∀ x : Option p4c11e_Sym, p4c11e_IsMid x →
        M.δ (.seekIn r) x = (.seekIn r, x, .left) := by
      intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hL : M.run (midL.reverse.length + 1)
        { state := .seekIn r,
          left := midL.reverse ++ (some .inU :: (List.replicate u (some .inU) ++ [some .inFirst])),
          head := v, right := midR ++ R_blank } =
        { state := .seekIn r, left := List.replicate u (some .inU) ++ [some .inFirst],
          head := some .inU, right := midL ++ [v] ++ midR ++ R_blank } := by
      have h0 := p4c11e_scanLeft M (.seekIn r)
        ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
         (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩ id midL.reverse v
        (some .inU) (hseek_d v hv_mid) (fun z hz => hseek_d z (hML_mid z hz))
        (List.replicate u (some .inU) ++ [some .inFirst]) (midR ++ R_blank)
      simpa [List.append_assoc] using h0
    rw [hmid, List.append_assoc] at hL
    let mid := List.replicate d (some .inDone) ++ (some .sep :: S_rest)
    have hstep_inU : M.step
        { state := .seekIn r, left := List.replicate u (some .inU) ++ [some .inFirst],
          head := some .inU, right := mid ++ R_blank } =
        { state := .emitNxt r,
          left := some .inDone :: List.replicate u (some .inU) ++ [some .inFirst],
          head := (mid ++ R_blank).headD none, right := (mid ++ R_blank).tail } := by
      unfold TM.step TM.IsHalting M p4c11e_mulTM; rfl
    have hmid_ne : ∀ z ∈ mid, p4c11e_IsMid z := by
      intro z hz
      simp only [mid, List.mem_append, List.mem_replicate, List.mem_cons] at hz
      rcases hz with ⟨_, rfl⟩ | rfl | hz
      · left; rfl
      · right; left; rfl
      · exact hS z hz
    have hemit_scan := p4c11e_scanRight M (.emitNxt r)
      ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
       (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩ id mid
      (fun z hz => by
        obtain ⟨sym, hsym⟩ : ∃ s, z = some s := by
          rcases hmid_ne z hz with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
        rw [hsym]; rfl)
      (some .inDone :: List.replicate u (some .inU) ++ [some .inFirst]) R_blank
    have hRblank_hd : R_blank.headD none = none := by
      rcases hblank with rfl | rfl <;> rfl
    have hRblank_tl : R_blank.tail = [] := by
      rcases hblank with rfl | rfl <;> rfl
    rw [hRblank_hd, hRblank_tl] at hemit_scan
    have hmid_nonempty : mid ≠ [] := by
      intro h0
      have : (mid).length = 0 := by rw [h0]; rfl
      simp [mid] at this
    obtain ⟨v_last, mid_init, hmid_snoc⟩ : ∃ v_last mid_init, mid = mid_init ++ [v_last] :=
      ⟨mid.getLast hmid_nonempty, mid.dropLast, (List.dropLast_append_getLast hmid_nonempty).symm⟩
    have hrev_cons : mid.reverse = v_last :: mid_init.reverse := by
      rw [hmid_snoc, List.reverse_append]; rfl
    have hstep_emit : M.step
        { state := .emitNxt r,
          left := mid.reverse ++ (some .inDone :: List.replicate u (some .inU) ++ [some .inFirst]),
          head := none, right := [] } =
        { state := .seekIn r,
          left := (some .inDone :: mid_init).reverse ++ List.replicate u (some .inU) ++ [some .inFirst],
          head := v_last, right := [some .nxt] } := by
      rw [hrev_cons]
      unfold TM.step TM.IsHalting M p4c11e_mulTM
      simp [List.append_assoc]
    have hS' : ∀ z ∈ S_rest ++ [some .nxt], p4c11e_IsMid z := by
      intro z hz
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact hS z hz1
      · rw [List.mem_singleton.mp hz2]; right; right; right; right; rfl
    have hmid' : (some .inDone :: mid_init) ++ [v_last] ++ [some .nxt] =
        List.replicate (d + 1) (some .inDone) ++ (some .sep :: (S_rest ++ [some .nxt])) := by
      calc
        (some .inDone :: mid_init) ++ [v_last] ++ [some .nxt]
            = some .inDone :: (mid_init ++ [v_last]) ++ [some .nxt] := by simp [List.append_assoc]
        _ = some .inDone :: mid ++ [some .nxt] := by rw [← hmid_snoc]
        _ = List.replicate (d + 1) (some .inDone) ++ (some .sep :: (S_rest ++ [some .nxt])) := by
          simp [mid, List.replicate_succ, List.append_assoc]
    obtain ⟨steps_ih, hsteps_ih, hrun_ih⟩ :=
      ih (d + 1) (S_rest ++ [some .nxt]) (some .inDone :: mid_init) [some .nxt] v_last []
        hS' hmid' (Or.inl rfl)
    have hmid_len : midL.length ≤ d + 1 + S_rest.length := by
      have hlen := congrArg List.length hmid
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at hlen
      omega
    have hpre_steps : (midL.reverse.length + 1) + 1 + mid.length + 1 ≤
        2 * (d + 2 * (u + 1) + S_rest.length + 1) + 5 := by
      have hml : mid.length = d + 1 + S_rest.length := by simp [mid]; omega
      simp only [List.length_reverse]
      omega
    refine ⟨(midL.reverse.length + 1) + 1 + mid.length + 1 + steps_ih, ?_, ?_⟩
    · have hih_bd : steps_ih ≤ (u + 1) * (2 * (d + 1 + 2 * u + (S_rest ++ [some p4c11e_Sym.nxt]).length + 1) + 5) :=
        hsteps_ih
      have hlen_sr : (S_rest ++ [some p4c11e_Sym.nxt]).length = S_rest.length + 1 := by simp
      rw [hlen_sr] at hih_bd
      have hinv : d + 1 + 2 * u + (S_rest.length + 1) + 1 = d + 2 * (u + 1) + S_rest.length + 1 := by omega
      rw [hinv] at hih_bd
      calc
        (midL.reverse.length + 1) + 1 + mid.length + 1 + steps_ih
            ≤ (2 * (d + 2 * (u + 1) + S_rest.length + 1) + 5) +
              (u + 1) * (2 * (d + 2 * (u + 1) + S_rest.length + 1) + 5) := Nat.add_le_add hpre_steps hih_bd
        _ = (u + 1 + 1) * (2 * (d + 2 * (u + 1) + S_rest.length + 1) + 5) := by ring
    · have h1 : M.run ((midL.reverse.length + 1) + 1 + mid.length + 1)
          { state := .seekIn r,
            left := midL.reverse ++ List.replicate (u + 1) (some .inU) ++ [some .inFirst],
            head := v, right := midR ++ R_blank } =
          { state := .seekIn r,
            left := (some .inDone :: mid_init).reverse ++ List.replicate u (some .inU) ++ [some .inFirst],
            head := v_last, right := [some .nxt] } := by
        have hL' : M.run (midL.reverse.length + 1)
            { state := .seekIn r,
              left := midL.reverse ++ (some .inU :: (List.replicate u (some .inU) ++ [some .inFirst])),
              head := v, right := midR ++ R_blank } =
            { state := .seekIn r,
              left := List.replicate u (some .inU) ++ [some .inFirst],
              head := some .inU, right := mid ++ R_blank } := by
          simpa [mid, List.append_assoc] using hL
        simp only [List.map_id] at hemit_scan
        have hstep_inU_run : M.run 1
            { state := .seekIn r, left := List.replicate u (some .inU) ++ [some .inFirst],
              head := some .inU, right := mid ++ R_blank } =
            { state := .emitNxt r,
              left := some .inDone :: List.replicate u (some .inU) ++ [some .inFirst],
              head := (mid ++ R_blank).headD none, right := (mid ++ R_blank).tail } := by
          rw [p4c11e_run_succ, hstep_inU, p4c11e_run_zero]
        have hstep_emit_run : M.run 1
            { state := .emitNxt r,
              left := mid.reverse ++ (some .inDone :: List.replicate u (some .inU) ++ [some .inFirst]),
              head := none, right := [] } =
            { state := .seekIn r,
              left := (some .inDone :: mid_init).reverse ++ List.replicate u (some .inU) ++ [some .inFirst],
              head := v_last, right := [some .nxt] } := by
          rw [p4c11e_run_succ, hstep_emit, p4c11e_run_zero]
        rw [List.replicate_succ]
        simp only [List.cons_append, List.append_assoc]
        rw [p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, hL', hstep_inU_run, hemit_scan, hstep_emit_run]
        simp only [List.append_assoc]
      rw [p4c11e_run_add, h1]
      have hd1 : d + 1 + u = d + (u + 1) := by omega
      simpa [M, List.replicate_succ, List.append_assoc, hd1] using hrun_ih

lemma p4c11e_findTokScan_skip (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (r : Fin b)
    (B : List (Option p4c11e_Sym))
    (hB : ∀ z ∈ B, z = some .nxt ∨ z = some .tokDone)
    (b_stop : Option p4c11e_Sym) (L R0 : List (Option p4c11e_Sym)) :
    (p4c11e_mulTM a b c ha hb).run B.length
      { state := .findTokScan r,
        left := (B.reverse ++ (b_stop :: L)).tail,
        head := (B.reverse ++ (b_stop :: L)).headD none,
        right := R0 } =
    { state := .findTokScan r, left := L, head := b_stop, right := B ++ R0 } := by
  let M := p4c11e_mulTM a b c ha hb
  cases B using List.reverseRecOn with
  | nil => simp [p4c11e_run_zero]
  | append_singleton B_init v =>
    have hlen : (B_init ++ [v]).length = B_init.reverse.length + 1 := by simp
    have hv : v = some .nxt ∨ v = some .tokDone := hB v (by simp)
    have hBi : ∀ z ∈ B_init.reverse, z = some .nxt ∨ z = some .tokDone :=
      fun z hz => hB z (by simp [List.mem_reverse.mp hz])
    have hstep_d : ∀ x : Option p4c11e_Sym, x = some .nxt ∨ x = some .tokDone →
        M.δ (.findTokScan r) x = (.findTokScan r, x, .left) := by
      intro x hx; rcases hx with rfl | rfl <;> rfl
    rw [hlen]
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append,
      List.tail_cons, List.headD_cons]
    have h0 := p4c11e_scanLeft M (.findTokScan r)
      ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
       (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩ id B_init.reverse v b_stop
      (hstep_d v hv) (fun z hz => hstep_d z (hBi z hz)) L R0
    simpa [List.append_assoc] using h0

lemma p4c11e_round_toks_loop (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (r : Fin b) (n : ℕ)
    (hn : 1 ≤ n) :
    ∀ (k s t m : ℕ) (_hktm : 1 ≤ k + t + m),
    ∃ steps, steps ≤ (k + 1) * (2 * (s + k + t + m + k * n + n + 10) * (n + 5) + 100) ∧
      (p4c11e_mulTM a b c ha hb).run steps
        { state := .findTokScan r,
          left := (List.replicate m (some p4c11e_Sym.nxt) ++ List.replicate t (some p4c11e_Sym.tokDone) ++
            List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
          head := (List.replicate m (some p4c11e_Sym.nxt) ++ List.replicate t (some p4c11e_Sym.tokDone) ++
            List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
          right := [none] } =
      { state := .promote r,
        left := List.replicate (m + k * n) (some p4c11e_Sym.tok) ++ List.replicate (s + 1 + t + k) (some p4c11e_Sym.sep) ++
          List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst],
        head := none, right := [] } := by
  let M := p4c11e_mulTM a b c ha hb
  intro k
  induction k with
  | zero =>
    intro s t m _hktm
    let B := List.replicate t (some p4c11e_Sym.tokDone) ++ List.replicate m (some p4c11e_Sym.nxt)
    have hB : ∀ z ∈ B, z = some .nxt ∨ z = some .tokDone := by
      intro z hz
      rcases List.mem_append.mp hz with h1 | h2
      · right; exact (List.mem_replicate.mp h1).2
      · left; exact (List.mem_replicate.mp h2).2
    have hBrev : B.reverse = List.replicate m (some .nxt) ++ List.replicate t (some .tokDone) := by
      simp [B, List.reverse_append, List.reverse_replicate]
    have hscan := p4c11e_findTokScan_skip a b c ha hb r B hB (some .sep)
      (List.replicate s (some .sep) ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst]) [none]
    have hstep_sep : M.step
        { state := .findTokScan r,
          left := List.replicate s (some .sep) ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst],
          head := some .sep, right := B ++ [none] } =
        { state := .promote r,
          left := List.replicate (s + 1) (some .sep) ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst],
          head := (B ++ [none]).headD none, right := (B ++ [none]).tail } := by
      unfold TM.step TM.IsHalting M p4c11e_mulTM
      simp [List.replicate_succ, List.append_assoc]
    have hprom := p4c11e_scanRight M (.promote r)
      ⟨(by dsimp [M, p4c11e_mulTM]; intro h; cases h),
       (by dsimp [M, p4c11e_mulTM]; intro h; cases h)⟩
      (fun x => if x = some .tokDone then some .sep else some .tok) B
      (fun z hz => by
        rcases hB z hz with rfl | rfl <;> rfl)
      (List.replicate (s + 1) (some .sep) ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst]) [none]
    have hmapB : (B.map (fun x => if x = some p4c11e_Sym.tokDone then some p4c11e_Sym.sep else some p4c11e_Sym.tok)).reverse =
        List.replicate m (some p4c11e_Sym.tok) ++ List.replicate t (some p4c11e_Sym.sep) := by
      simp [B, List.map_append, List.map_replicate, List.reverse_append, List.reverse_replicate]
    have hlenB : B.length = t + m := by simp [B]
    refine ⟨B.length + 1 + B.length, ?_, ?_⟩
    · rw [hlenB]; nlinarith
    · rw [p4c11e_run_add, p4c11e_run_add]
      have hstart : (List.replicate m (some .nxt) ++ List.replicate t (some .tokDone) ++
            List.replicate 0 (some .tok) ++ List.replicate (s + 1) (some .sep) ++
            List.replicate (n - 1) (some .inU) ++ [some .inFirst]) =
          B.reverse ++ (some .sep :: (List.replicate s (some .sep) ++
            List.replicate (n - 1) (some .inU) ++ [some .inFirst])) := by
        rw [hBrev]
        simp [List.replicate_succ, List.append_assoc]
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [hstart, hscan, p4c11e_run_succ, hstep_sep, p4c11e_run_zero, hprom, hmapB]
      have hrepl_sep : List.replicate t (some p4c11e_Sym.sep) ++
          (List.replicate (s + 1) (some p4c11e_Sym.sep) ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++
            [some p4c11e_Sym.inFirst]) =
          List.replicate (s + 1 + t) (some p4c11e_Sym.sep) ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++
            [some p4c11e_Sym.inFirst] := by
        have ht_comm : t + (s + 1) = s + 1 + t := by omega
        simp only [← List.append_assoc, ← List.replicate_add, ht_comm]
      rw [List.append_assoc, hrepl_sep]
      simp only [List.headD_cons, List.tail_cons, List.append_assoc]
  | succ k ih =>
    intro s t m _
    let B := List.replicate t (some p4c11e_Sym.tokDone) ++ List.replicate m (some p4c11e_Sym.nxt)
    have hB : ∀ z ∈ B, z = some .nxt ∨ z = some .tokDone := by
      intro z hz
      rcases List.mem_append.mp hz with h1 | h2
      · right; exact (List.mem_replicate.mp h1).2
      · left; exact (List.mem_replicate.mp h2).2
    have hBrev : B.reverse = List.replicate m (some .nxt) ++ List.replicate t (some .tokDone) := by
      simp [B, List.reverse_append, List.reverse_replicate]
    let L_tok := List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
      List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]
    have hscan := p4c11e_findTokScan_skip a b c ha hb r B hB (some .tok) L_tok [none]
    let mid_pref_rev := List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep)
    have hmp_nonempty : mid_pref_rev ≠ [] := by
      intro h0
      have : mid_pref_rev.length = 0 := by rw [h0]; rfl
      simp [mid_pref_rev] at this
    let v0 := mid_pref_rev.head hmp_nonempty
    let mp_tail := mid_pref_rev.tail
    have hmp_cons : mid_pref_rev = v0 :: mp_tail := (List.cons_head_tail hmp_nonempty).symm
    have hstep_tok : M.step
        { state := .findTokScan r, left := L_tok, head := some .tok, right := B ++ [none] } =
        { state := .seekIn r,
          left := mp_tail ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst],
          head := v0, right := some .tokDone :: B ++ [none] } := by
      have hL' : L_tok = (v0 :: mp_tail) ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst] := by
        rw [← hmp_cons]
      rw [hL']
      unfold TM.step TM.IsHalting M p4c11e_mulTM
      simp [List.append_assoc]
    have hmp_rev_eq : mid_pref_rev.reverse =
        some .sep :: (List.replicate s (some .sep) ++ List.replicate k (some .tok)) := by
      have h1 : List.replicate (s + 1) (some p4c11e_Sym.sep) =
          some p4c11e_Sym.sep :: List.replicate s (some p4c11e_Sym.sep) := rfl
      simp only [mid_pref_rev, List.reverse_append, List.reverse_replicate]
      rw [h1, List.cons_append]
    let S_rest := List.replicate s (some .sep) ++ List.replicate k (some .tok) ++
      (some .tokDone :: B)
    have hSrest_mid : ∀ z ∈ S_rest, p4c11e_IsMid z := by
      intro z hz
      simp only [S_rest, B, List.mem_append, List.mem_replicate, List.mem_cons] at hz
      rcases hz with (⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · right; left; rfl
      · right; right; left; rfl
      · right; right; right; left; rfl
      · right; right; right; left; rfl
      · right; right; right; right; rfl
    have hmid_seek : mp_tail.reverse ++ [v0] ++ (some .tokDone :: B) =
        List.replicate 0 (some .inDone) ++ (some .sep :: S_rest) := by
      calc
        mp_tail.reverse ++ [v0] ++ (some .tokDone :: B)
            = (v0 :: mp_tail).reverse ++ (some .tokDone :: B) := by simp
        _ = mid_pref_rev.reverse ++ (some .tokDone :: B) := by rw [← hmp_cons]
        _ = (some .sep :: (List.replicate s (some .sep) ++ List.replicate k (some .tok))) ++
              (some .tokDone :: B) := by rw [hmp_rev_eq]
        _ = List.replicate 0 (some .inDone) ++ (some .sep :: S_rest) := by
          simp [S_rest, List.append_assoc]
    obtain ⟨steps_seek, hsteps_seek, hrun_seek⟩ :=
      p4c11e_seekIn_loop a b c ha hb r (n - 1) 0 S_rest mp_tail.reverse (some .tokDone :: B) v0 [none]
        hSrest_mid hmid_seek (Or.inr rfl)
    have hstep_ft : M.step
        { state := .findTok r,
          left := (S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
            [some p4c11e_Sym.sep] ++ List.replicate (0 + (n - 1)) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst],
          head := none, right := [] } =
        { state := .findTokScan r,
          left := ((S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
            [some p4c11e_Sym.sep] ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
          head := ((S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
            [some p4c11e_Sym.sep] ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
          right := [none] } := by
      have hne : ((S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
            [some p4c11e_Sym.sep] ++ List.replicate (0 + (n - 1)) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]) ≠ [] := by
        simp
      have hhd := List.cons_head_tail hne
      unfold TM.step TM.IsHalting M p4c11e_mulTM
      cases hLcase : (S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
          [some p4c11e_Sym.sep] ++ List.replicate (0 + (n - 1)) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst] with
      | nil => simp at hLcase
      | cons x xs =>
        have hL_rew : (S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
            [some p4c11e_Sym.sep] ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++
            [some p4c11e_Sym.inFirst] = x :: xs := by
          simpa [Nat.zero_add] using hLcase
        rw [hL_rew]
        simp
    have hnxt_eq : (S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
          [some p4c11e_Sym.sep] ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst] =
        List.replicate (m + n) (some p4c11e_Sym.nxt) ++ List.replicate (t + 1) (some p4c11e_Sym.tokDone) ++
          List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
          List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst] := by
      have hn1 : (n - 1) + 1 = n := by omega
      have hmn : m + n = n + m := Nat.add_comm m n
      rw [hn1, hmn, List.replicate_add, List.replicate_succ' (n := t), List.replicate_succ' (n := s)]
      simp only [S_rest, B, List.reverse_append, List.reverse_cons, List.reverse_replicate,
        List.append_assoc]
    obtain ⟨steps_ih, hsteps_ih, hrun_ih⟩ := ih s (t + 1) (m + n) (by omega)
    have hSrest_len : S_rest.length = s + k + 1 + t + m := by
      simp [S_rest, B]; omega
    have hpre_bound : B.length + 1 + steps_seek + 1 ≤
        2 * (s + (k + 1) + t + m + (k + 1) * n + n + 10) * (n + 5) + 100 := by
      have hlenB : B.length = t + m := by simp [B]
      have hseek' : steps_seek ≤ n * (2 * (2 * n + S_rest.length + 1) + 5) := by
        calc
          steps_seek ≤ (n - 1 + 1) * (2 * (0 + 2 * (n - 1) + S_rest.length + 1) + 5) := hsteps_seek
          _ ≤ n * (2 * (2 * n + S_rest.length + 1) + 5) := by
            gcongr <;> omega
      rw [hSrest_len] at hseek'
      rw [hlenB]
      have hkn : 2 * n ≤ (k + 1) * n + n := by
        have : n ≤ (k + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos k)
        omega
      have hdom_id : 2 * (s + (k + 1) + t + m + 2 * n + 10) * (n + 5) + 100 =
          (t + m + 1 + n * (2 * (2 * n + (s + k + 1 + t + m) + 1) + 5) + 1) +
            (10 * s + 10 * k + 9 * t + 9 * m + 33 * n + 208) := by ring
      have hinner_le : s + (k + 1) + t + m + 2 * n + 10 ≤
          s + (k + 1) + t + m + (k + 1) * n + n + 10 := by omega
      have hmono : 2 * (s + (k + 1) + t + m + 2 * n + 10) * (n + 5) + 100 ≤
          2 * (s + (k + 1) + t + m + (k + 1) * n + n + 10) * (n + 5) + 100 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right (n + 5) (Nat.mul_le_mul_left 2 hinner_le)) 100
      omega
    refine ⟨(B.length + 1 + steps_seek + 1) + steps_ih, ?_, ?_⟩
    · have hsum_ih : s + k + (t + 1) + (m + n) + k * n + n + 10 =
          s + (k + 1) + t + m + (k + 1) * n + n + 10 := by ring
      have hih' : steps_ih ≤ (k + 1) *
          (2 * (s + (k + 1) + t + m + (k + 1) * n + n + 10) * (n + 5) + 100) := by
        rw [← hsum_ih]
        exact hsteps_ih
      nlinarith [hpre_bound, hih']
    · have hstart : List.replicate m (some .nxt) ++ List.replicate t (some .tokDone) ++
            List.replicate (k + 1) (some .tok) ++ List.replicate (s + 1) (some .sep) ++
            List.replicate (n - 1) (some .inU) ++ [some .inFirst] =
          B.reverse ++ (some .tok :: L_tok) := by
        rw [hBrev]
        simp [L_tok, List.replicate_succ, List.append_assoc]
      have hphase1 : M.run (B.length + 1 + steps_seek + 1)
          { state := .findTokScan r,
            left := (B.reverse ++ (some p4c11e_Sym.tok :: L_tok)).tail,
            head := (B.reverse ++ (some p4c11e_Sym.tok :: L_tok)).headD none,
            right := [none] } =
          { state := .findTokScan r,
            left := (List.replicate (m + n) (some p4c11e_Sym.nxt) ++
              List.replicate (t + 1) (some p4c11e_Sym.tokDone) ++
              List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
            head := (List.replicate (m + n) (some p4c11e_Sym.nxt) ++
              List.replicate (t + 1) (some p4c11e_Sym.tokDone) ++
              List.replicate k (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
            right := [none] } := by
        have hstep_tok_run : M.run 1
            { state := .findTokScan r, left := L_tok, head := some .tok, right := B ++ [none] } =
            { state := .seekIn r,
              left := mp_tail ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst],
              head := v0, right := some .tokDone :: B ++ [none] } := by
          rw [p4c11e_run_succ, hstep_tok, p4c11e_run_zero]
        have hstep_ft_run : M.run 1
            { state := .findTok r,
              left := (S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
                [some p4c11e_Sym.sep] ++ List.replicate (0 + (n - 1)) (some p4c11e_Sym.inU) ++
                [some p4c11e_Sym.inFirst],
              head := none, right := [] } =
            { state := .findTokScan r,
              left := ((S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
                [some p4c11e_Sym.sep] ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++
                [some p4c11e_Sym.inFirst]).tail,
              head := ((S_rest ++ List.replicate ((n - 1) + 1) (some p4c11e_Sym.nxt)).reverse ++
                [some p4c11e_Sym.sep] ++ List.replicate (n - 1) (some p4c11e_Sym.inU) ++
                [some p4c11e_Sym.inFirst]).headD none,
              right := [none] } := by
          rw [p4c11e_run_succ, hstep_ft, p4c11e_run_zero]
        have hseek_rw : mp_tail ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst] =
            mp_tail.reverse.reverse ++ List.replicate (n - 1) (some .inU) ++ [some .inFirst] := by
          simp
        rw [p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, hscan, hstep_tok_run,
          hseek_rw, show some .tokDone :: B ++ [none] = (some .tokDone :: B) ++ [none] by rfl,
          hrun_seek, hstep_ft_run, hnxt_eq]
      have hm_eq : m + n + k * n = m + (k + 1) * n := by ring
      have hs_eq : s + 1 + (t + 1) + k = s + 1 + t + (k + 1) := by omega
      rw [p4c11e_run_add, hstart, hphase1, hrun_ih, hm_eq, hs_eq]

lemma p4c11e_rounds_loop (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) (hn : 1 ≤ n) :
    ∀ (r s : ℕ) (hr : r < b),
    ∃ steps s',
      steps ≤ (r + 1) * ((a * n ^ b + 1) *
        (2 * (s + (r + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10) ∧
      s' ≤ s + (r + 1) * a * n ^ b ∧
      (p4c11e_mulTM a b c ha hb).run steps
        { state := .findTokScan ⟨0, by omega⟩,
          left := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
          head := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++ List.replicate (s + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
          right := [none] } =
      { state := .promote ⟨r, hr⟩,
        left := List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++ List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
          List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst],
        head := none, right := [] } := by
  let M := p4c11e_mulTM a b c ha hb
  intro r
  induction r with
  | zero =>
    intro s hr
    have hpow0 : a * n ^ 0 = a := by simp
    have hpow1 : a * n ^ 1 = a * n := by simp
    have hk_pos : 1 ≤ a * n ^ 0 + 0 + 0 := by omega
    obtain ⟨steps_tok, hsteps_tok, hrun_tok⟩ :=
      p4c11e_round_toks_loop a b c ha hb ⟨0, hr⟩ n hn (a * n ^ 0) s 0 0 hk_pos
    have hpow_le : n ^ 0 ≤ n ^ b := Nat.pow_le_pow_right hn (Nat.zero_le b)
    have hpow_le1 : n ^ 1 ≤ n ^ b := Nat.pow_le_pow_right hn hb
    refine ⟨steps_tok, s + a * n ^ 0, ?_, ?_, ?_⟩
    · have h1 : a * n ^ 0 ≤ a * n ^ b := Nat.mul_le_mul_left a hpow_le
      have h2 : a * n ^ 0 * n ≤ a * n ^ b := by
        rw [hpow0, ← hpow1]; exact Nat.mul_le_mul_left a hpow_le1
      have hinner : s + a * n ^ 0 + 0 + 0 + a * n ^ 0 * n + n + 10 ≤
          s + (0 + 1) * a * n ^ b + a * n ^ b + n + 30 := by
        simp only [Nat.zero_add, Nat.add_zero, one_mul]
        omega
      have hsub : (a * n ^ 0 + 1) *
          (2 * (s + a * n ^ 0 + 0 + 0 + a * n ^ 0 * n + n + 10) * (n + 5) + 100) ≤
          (a * n ^ b + 1) *
          (2 * (s + (0 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) :=
        Nat.mul_le_mul (Nat.add_le_add_right h1 1)
          (Nat.add_le_add_right (Nat.mul_le_mul_right (n + 5) (Nat.mul_le_mul_left 2 hinner)) 100)
      have hone : (0 + 1) * ((a * n ^ b + 1) *
          (2 * (s + (0 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10) =
          (a * n ^ b + 1) *
          (2 * (s + (0 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10 := by simp
      rw [hone]
      exact le_trans hsteps_tok (le_trans hsub (Nat.le_add_right _ 10))
    · have h1 : a * n ^ 0 ≤ a * n ^ b := Nat.mul_le_mul_left a hpow_le
      simp only [Nat.zero_add, one_mul]
      omega
    · simpa [List.replicate_zero, List.nil_append, List.append_assoc, Nat.pow_succ, Nat.mul_assoc,
        Nat.add_assoc, Nat.add_comm 1 a] using hrun_tok
  | succ r ih =>
    intro s hr
    have hr0 : r < b := Nat.lt_of_succ_lt hr
    obtain ⟨steps_prev, s', hsteps_prev, hs', hrun_prev⟩ := ih s hr0
    have hstep_prom : M.step
        { state := .promote ⟨r, hr0⟩,
          left := List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
            List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst],
          head := none, right := [] } =
        { state := .findTokScan ⟨r + 1, hr⟩,
          left := (List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
            List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
          head := (List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
            List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
          right := [none] } := by
      have hne : List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
          List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
          List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst] ≠ [] := by simp
      unfold TM.step TM.IsHalting M p4c11e_mulTM
      cases hLcase : List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
          List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
          List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst] with
      | nil => simp at hLcase
      | cons x xs => simp [hr]
    have hpow_pos : 1 ≤ a * n ^ (r + 1) := Nat.mul_pos ha (Nat.pow_pos hn)
    obtain ⟨steps_tok, hsteps_tok, hrun_tok⟩ :=
      p4c11e_round_toks_loop a b c ha hb ⟨r + 1, hr⟩ n hn (a * n ^ (r + 1)) s' 0 0 (by omega)
    have hpow_le_r : n ^ (r + 1) ≤ n ^ b := Nat.pow_le_pow_right hn hr.le
    have hpow_le_next : n ^ (r + 2) ≤ n ^ b := by
      by_cases hrb : r + 2 ≤ b
      · exact Nat.pow_le_pow_right hn hrb
      · exfalso; omega
    have hs'_bound : s' ≤ s + (r + 1) * a * n ^ b := hs'
    have hsteps_tok' : steps_tok ≤ (a * n ^ b + 1) *
        (2 * (s + (r + 1 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) := by
      refine le_trans hsteps_tok ?_
      simp only [Nat.add_zero]
      have ha1 : a * n ^ (r + 1) ≤ a * n ^ b := Nat.mul_le_mul_left a hpow_le_r
      have ha2 : a * n ^ (r + 1) * n ≤ a * n ^ b := by
        calc
          a * n ^ (r + 1) * n = a * n ^ (r + 2) := by rw [Nat.pow_succ]; ring
          _ ≤ a * n ^ b := Nat.mul_le_mul_left a hpow_le_next
      have hr_ring : (r + 1 + 1) * a * n ^ b = (r + 1) * a * n ^ b + a * n ^ b := by ring
      have hinner : s' + a * n ^ (r + 1) + a * n ^ (r + 1) * n + n + 10 ≤
          s + (r + 1 + 1) * a * n ^ b + a * n ^ b + n + 30 := by
        linarith [hs'_bound, ha1, ha2, hr_ring]
      exact Nat.mul_le_mul (Nat.add_le_add_right ha1 1)
        (Nat.add_le_add_right (Nat.mul_le_mul_right (n + 5) (Nat.mul_le_mul_left 2 hinner)) 100)
    have hsteps_prev' : steps_prev ≤ (r + 1) * ((a * n ^ b + 1) *
        (2 * (s + (r + 1 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10) := by
      refine le_trans hsteps_prev ?_
      gcongr
      omega
    refine ⟨steps_prev + 1 + steps_tok, s' + a * n ^ (r + 1), ?_, ?_, ?_⟩
    · have hsum_bd : steps_prev + 1 + steps_tok ≤
          (r + 1) * ((a * n ^ b + 1) *
            (2 * (s + (r + 1 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10) +
          ((a * n ^ b + 1) *
            (2 * (s + (r + 1 + 1) * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10) := by
        omega
      simpa [Nat.succ_mul] using hsum_bd
    · have ha1 : a * n ^ (r + 1) ≤ a * n ^ b := Nat.mul_le_mul_left a hpow_le_r
      have : s + (r + 1) * a * n ^ b + a * n ^ b = s + (r + 1 + 1) * a * n ^ b := by ring
      omega
    · have hstep_prom_run : (p4c11e_mulTM a b c ha hb).run 1
          { state := .promote ⟨r, hr0⟩,
            left := List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
              List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst],
            head := none, right := [] } =
          { state := .findTokScan ⟨r + 1, hr⟩,
            left := (List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
              List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
            head := (List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
              List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
            right := [none] } := by
        rw [p4c11e_run_succ, hstep_prom, p4c11e_run_zero]
      have hp1 : a * n ^ (r + 1) * n = a * n ^ (r + 1 + 1) := by rw [Nat.pow_succ]; ring
      have hs1 : s' + 1 + 0 + a * n ^ (r + 1) = s' + a * n ^ (r + 1) + 1 := by omega
      have hrun_tok' : (p4c11e_mulTM a b c ha hb).run steps_tok
          { state := .findTokScan ⟨r + 1, hr⟩,
            left := (List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
              List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
            head := (List.replicate (a * n ^ (r + 1)) (some p4c11e_Sym.tok) ++
              List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
            right := [none] } =
          { state := .promote ⟨r + 1, hr⟩,
            left := List.replicate (a * n ^ (r + 1 + 1)) (some p4c11e_Sym.tok) ++
              List.replicate (s' + a * n ^ (r + 1) + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst],
            head := none, right := [] } := by
        simpa [List.replicate_zero, List.nil_append, List.append_assoc, hp1, hs1] using hrun_tok
      rw [p4c11e_run_add, p4c11e_run_add, hrun_prev, hstep_prom_run, hrun_tok']

lemma p4c11e_appendC_loop (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∀ (d j : ℕ) (hd : 1 ≤ d) (hjc : j + d = c)
      (L_hd : Option p4c11e_Sym) (L_tl : List (Option p4c11e_Sym)),
    (p4c11e_mulTM a b c ha hb).run d
      { state := .appendC ⟨j, by omega⟩, left := L_hd :: L_tl, head := none, right := [] } =
    { state := .finalizeScan,
      left := (List.replicate (d - 1) (some (p4c11e_Sym.bit true)) ++ (L_hd :: L_tl)).tail,
      head := (List.replicate (d - 1) (some (p4c11e_Sym.bit true)) ++ (L_hd :: L_tl)).headD none,
      right := [some (p4c11e_Sym.bit true)] } := by
  let M := p4c11e_mulTM a b c ha hb
  intro d
  induction d with
  | zero => intro _ hd; omega
  | succ d ih =>
    intro j _ hjc L_hd L_tl
    rw [p4c11e_run_succ]
    by_cases hd0 : d = 0
    · subst hd0
      have hstep : M.step
          { state := .appendC ⟨j, by omega⟩, left := L_hd :: L_tl,
            head := none, right := [] } =
          { state := .finalizeScan, left := L_tl, head := L_hd,
            right := [some (p4c11e_Sym.bit true)] } := by
        unfold TM.step TM.IsHalting M p4c11e_mulTM
        have hfalse : ¬ (j + 1 < c) := by omega
        simp [hfalse]
      rw [hstep, p4c11e_run_zero]
      simp
    · have hd1 : 1 ≤ d := by omega
      have hlt : j + 1 < c := by omega
      have hstep : M.step
          { state := .appendC ⟨j, by omega⟩, left := L_hd :: L_tl,
            head := none, right := [] } =
          { state := .appendC ⟨j + 1, hlt⟩,
            left := some (p4c11e_Sym.bit true) :: L_hd :: L_tl,
            head := none, right := [] } := by
        unfold TM.step TM.IsHalting M p4c11e_mulTM
        simp [hlt]
      have hstep' : (p4c11e_mulTM a b c ha hb).step
          { state := .appendC ⟨j, by omega⟩, left := L_hd :: L_tl,
            head := none, right := [] } =
          { state := .appendC ⟨j + 1, hlt⟩,
            left := some (p4c11e_Sym.bit true) :: L_hd :: L_tl,
            head := none, right := [] } := hstep
      rw [hstep', ih (j + 1) hd1 (by omega) (some (p4c11e_Sym.bit true)) (L_hd :: L_tl)]
      have hrepl : List.replicate (d - 1) (some (p4c11e_Sym.bit true)) ++
          [some (p4c11e_Sym.bit true)] =
          List.replicate d (some (p4c11e_Sym.bit true)) := by
        rw [← List.replicate_succ']; congr 1; omega
      have hrepl' : List.replicate (d - 1) (some (p4c11e_Sym.bit true)) ++
          some (p4c11e_Sym.bit true) :: L_hd :: L_tl =
          List.replicate d (some (p4c11e_Sym.bit true)) ++ L_hd :: L_tl := by
        rw [show some (p4c11e_Sym.bit true) :: L_hd :: L_tl =
          [some (p4c11e_Sym.bit true)] ++ (L_hd :: L_tl) from rfl, ← List.append_assoc, hrepl]
      simp only [Nat.add_sub_cancel]
      rw [hrepl']

lemma p4c11e_finalize (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (T_tok T_bit : ℕ) (hnonempty : 1 ≤ T_tok + T_bit)
    (L_rest R_end : List (Option p4c11e_Sym))
    (_hRend : R_end = [none] ∨ R_end = [some (.bit true)]) :
    (p4c11e_mulTM a b c ha hb).run (T_bit + T_tok + 1)
      { state := .finalizeScan,
        left := (List.replicate T_bit (some (p4c11e_Sym.bit true)) ++
          List.replicate T_tok (some p4c11e_Sym.tok) ++ (some p4c11e_Sym.sep :: L_rest)).tail,
        head := (List.replicate T_bit (some (p4c11e_Sym.bit true)) ++
          List.replicate T_tok (some p4c11e_Sym.tok) ++ (some p4c11e_Sym.sep :: L_rest)).headD none,
        right := R_end } =
    { state := .accept,
      left := some p4c11e_Sym.sep :: L_rest,
      head := some (p4c11e_Sym.bit true),
      right := List.replicate (T_tok + T_bit - 1) (some (p4c11e_Sym.bit true)) ++ R_end } := by
  let M := p4c11e_mulTM a b c ha hb
  let B := List.replicate T_tok (some p4c11e_Sym.tok) ++ List.replicate T_bit (some (p4c11e_Sym.bit true))
  have hB_nonempty : B ≠ [] := by
    intro h0
    have hlen := congrArg List.length h0
    simp [B] at hlen
    omega
  let B_init := B.dropLast
  let v := B.getLast hB_nonempty
  have hB_snoc : B = B_init ++ [v] := (List.dropLast_append_getLast hB_nonempty).symm
  have hB_mem : ∀ z ∈ B, z = some (.bit true) ∨ z = some .tok := by
    intro z hz
    rcases List.mem_append.mp hz with h1 | h2
    · right; exact (List.mem_replicate.mp h1).2
    · left; exact (List.mem_replicate.mp h2).2
  have hv_mem : v = some (.bit true) ∨ v = some .tok := hB_mem v (List.getLast_mem hB_nonempty)
  have hBi_rev : ∀ z ∈ B_init.reverse, z = some (.bit true) ∨ z = some .tok := fun z hz =>
    hB_mem z (by rw [hB_snoc]; simp [List.mem_reverse.mp hz])
  have hstep_fin : ∀ x : Option p4c11e_Sym, x = some (.bit true) ∨ x = some .tok →
      M.δ .finalizeScan x = (.finalizeScan, some (.bit true), .left) := by
    intro x hx; rcases hx with rfl | rfl <;> rfl
  have hq : (.finalizeScan : p4c11e_MulQ a b c) ≠ M.qaccept ∧
      (.finalizeScan : p4c11e_MulQ a b c) ≠ M.qreject := by
    dsimp [M, p4c11e_mulTM]
    constructor
    · intro h; cases h
    · intro h; cases h
  have hscan := p4c11e_scanLeft M .finalizeScan hq
    (fun _ => some (p4c11e_Sym.bit true))
    B_init.reverse v (some .sep) (hstep_fin v hv_mem) (fun z hz => hstep_fin z (hBi_rev z hz))
    L_rest R_end
  have hBrev_eq : B.reverse = List.replicate T_bit (some (p4c11e_Sym.bit true)) ++
      List.replicate T_tok (some p4c11e_Sym.tok) := by
    simp [B, List.reverse_append, List.reverse_replicate]
  have hmapB : (B_init.reverse.map (fun _ => some (p4c11e_Sym.bit true))).reverse ++
      [some (p4c11e_Sym.bit true)] =
      List.replicate (T_tok + T_bit) (some (p4c11e_Sym.bit true)) := by
    have hlen : B_init.length + 1 = B.length := by
      have := congrArg List.length hB_snoc; simp at this; omega
    have hBlen : B.length = T_tok + T_bit := by simp [B]
    simp only [List.map_reverse, List.reverse_reverse, List.map_const']
    rw [← List.replicate_succ', hlen, hBlen]
  have hlen_run : B_init.reverse.length + 1 = T_bit + T_tok := by
    have h1 := congrArg List.length hB_snoc
    have h2 : B.length = T_tok + T_bit := by simp [B]
    simp only [List.length_reverse, List.length_append, List.length_singleton] at h1 ⊢
    omega
  have hBrev_snoc : B.reverse = v :: B_init.reverse := by rw [hB_snoc, List.reverse_append]; rfl
  have hstep_sep : M.step
      { state := .finalizeScan, left := L_rest, head := some .sep,
        right := List.replicate (T_tok + T_bit) (some (.bit true)) ++ R_end } =
      { state := .accept, left := some .sep :: L_rest, head := some (.bit true),
        right := List.replicate (T_tok + T_bit - 1) (some (.bit true)) ++ R_end } := by
    have hrepl : List.replicate (T_tok + T_bit) (some (p4c11e_Sym.bit true)) =
        some (p4c11e_Sym.bit true) :: List.replicate (T_tok + T_bit - 1) (some (p4c11e_Sym.bit true)) := by
      conv_lhs => rw [show T_tok + T_bit = (T_tok + T_bit - 1) + 1 by omega]
      rw [List.replicate_succ]
    rw [hrepl]
    unfold TM.step TM.IsHalting M p4c11e_mulTM
    simp
  rw [p4c11e_run_add, ← hlen_run]
  rw [← hBrev_eq, hBrev_snoc, List.cons_append, List.tail_cons, List.headD_cons]
  rw [hscan, hmapB, p4c11e_run_succ, hstep_sep, p4c11e_run_zero]

lemma p4c11e_mulTM_spec (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    PolyTimeComputable (fun x : List Bool => unary (a * x.length ^ b + c)) := by
  let M := p4c11e_mulTM a b c ha hb
  let B₀ : ℕ := b * ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200) + 10) + 2 * a + 2 * c + 100
  let d : ℕ := 2 * b + 3
  let K : ℕ := d + 2 * B₀ + 2
  refine ⟨p4c11e_Sym, inferInstance, p4c11e_symEmb, p4c11e_symEmb, M, K, ?_⟩
  intro x
  by_cases hn : x.length = 0
  · have hx_nil : x = [] := List.length_eq_zero_iff.mp hn
    subst hx_nil
    simp only [List.length_nil, Nat.zero_pow (by omega : 0 < b), Nat.mul_zero, Nat.zero_add]
    by_cases hc : 0 < c
    · have hstep0 : M.step (M.init (([] : List Bool).map p4c11e_symEmb)) =
          { state := .appendC ⟨0, hc⟩, left := [some .sep], head := none, right := [] } := by
        unfold TM.step TM.IsHalting M p4c11e_mulTM TM.init
        simp [hc]
      have hstep0_1 : M.run 1 (M.init (([] : List Bool).map p4c11e_symEmb)) =
          { state := .appendC ⟨0, hc⟩, left := [some .sep], head := none, right := [] } := by
        rw [p4c11e_run_succ, hstep0, p4c11e_run_zero]
      by_cases hc1 : 1 < c
      · have happ := p4c11e_appendC_loop a b c ha hb c 0 hc (Nat.zero_add c) (some .sep) []
        have hfin := p4c11e_finalize a b c ha hb 0 (c - 1) (by omega) []
          [some (p4c11e_Sym.bit true)] (Or.inr rfl)
        have h1c : M.run (1 + c) (M.init (([] : List Bool).map p4c11e_symEmb)) =
            { state := .finalizeScan,
              left := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++ [some p4c11e_Sym.sep]).tail,
              head := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++ [some p4c11e_Sym.sep]).headD none,
              right := [some (p4c11e_Sym.bit true)] } := by
          have happ' : M.run c
              { state := .appendC ⟨0, hc⟩, left := [some .sep], head := none, right := [] } =
              { state := .finalizeScan,
                left := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++ [some p4c11e_Sym.sep]).tail,
                head := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++ [some p4c11e_Sym.sep]).headD none,
                right := [some (p4c11e_Sym.bit true)] } := happ
          rw [p4c11e_run_add, hstep0_1, happ']
        have hrun : M.run (1 + c + ((c - 1) + 0 + 1)) (M.init (([] : List Bool).map p4c11e_symEmb)) =
            { state := .accept, left := [some .sep], head := some (p4c11e_Sym.bit true),
              right := List.replicate (c - 2) (some (p4c11e_Sym.bit true)) ++ [some (p4c11e_Sym.bit true)] } := by
          have hfin' : M.run ((c - 1) + 0 + 1)
              { state := .finalizeScan,
                left := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++ [some p4c11e_Sym.sep]).tail,
                head := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++ [some p4c11e_Sym.sep]).headD none,
                right := [some (p4c11e_Sym.bit true)] } =
              { state := .accept, left := [some .sep], head := some (p4c11e_Sym.bit true),
                right := List.replicate (c - 2) (some (p4c11e_Sym.bit true)) ++ [some (p4c11e_Sym.bit true)] } := by
            have hfin_m : M.run ((c - 1) + 0 + 1)
                { state := .finalizeScan,
                  left := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++
                    List.replicate 0 (some p4c11e_Sym.tok) ++ [some p4c11e_Sym.sep]).tail,
                  head := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++
                    List.replicate 0 (some p4c11e_Sym.tok) ++ [some p4c11e_Sym.sep]).headD none,
                  right := [some (p4c11e_Sym.bit true)] } =
                { state := .accept, left := [some p4c11e_Sym.sep],
                  head := some (p4c11e_Sym.bit true),
                  right := List.replicate (0 + (c - 1) - 1) (some (p4c11e_Sym.bit true)) ++
                    [some (p4c11e_Sym.bit true)] } := hfin
            have hsub_c2 : 0 + (c - 1) - 1 = c - 2 := by omega
            rw [List.replicate_zero, List.append_nil, hsub_c2] at hfin_m
            exact hfin_m
          rw [p4c11e_run_add, h1c, hfin']
        have hhalt : M.HaltsWithin (1 + c + ((c - 1) + 0 + 1)) (([] : List Bool).map p4c11e_symEmb) := by
          unfold TM.HaltsWithin TM.IsHalting; rw [hrun]; left; rfl
        have hle : 1 + c + ((c - 1) + 0 + 1) ≤ 0 ^ K + K := by
          simp [K, B₀]; omega
        refine ⟨p4c11e_halts_mono M _ hle hhalt, ?_⟩
        rw [p4c11e_run_mono_output M _ hle hhalt, hrun]
        have hout := p4c11e_output_with_blanks M p4c11e_symEmb .accept [some .sep] (unary c) []
          (fun z hz => by simp at hz)
        have hrepl_c : List.replicate (c - 2) (some (p4c11e_Sym.bit true)) ++ [some (p4c11e_Sym.bit true)] =
            List.replicate (c - 1) (some (p4c11e_Sym.bit true)) := by
          rw [← List.replicate_succ']; congr 1; omega
        have huc : unary c = true :: List.replicate (c - 1) true := by
          unfold unary
          conv_lhs => rw [show c = (c - 1) + 1 by omega]
          rw [List.replicate_succ]
        rw [hrepl_c]
        have hcoe : (p4c11e_symEmb : Bool → p4c11e_Sym) = p4c11e_Sym.bit := rfl
        rw [huc, hcoe] at hout ⊢
        dsimp only at hout ⊢
        simp only [List.map_cons, Function.comp_apply, List.map_replicate, List.append_nil] at hout ⊢
        exact hout
      · have hc_eq1 : c = 1 := by omega
        have hstep1 : M.step
            { state := .appendC ⟨0, hc⟩, left := [some .sep], head := none, right := [] } =
            { state := .finalizeScan, left := [], head := some .sep,
              right := [some (p4c11e_Sym.bit true)] } := by
          unfold TM.step TM.IsHalting M p4c11e_mulTM
          simp [hc_eq1]
        have hstep2 : M.step
            { state := .finalizeScan, left := [], head := some .sep,
              right := [some (p4c11e_Sym.bit true)] } =
            { state := .accept, left := [some .sep], head := some (p4c11e_Sym.bit true),
              right := [] } := by
          unfold TM.step TM.IsHalting M p4c11e_mulTM
          rfl
        have hstep1_run : M.run 1
            { state := .appendC ⟨0, hc⟩, left := [some .sep], head := none, right := [] } =
            { state := .finalizeScan, left := [], head := some .sep,
              right := [some (p4c11e_Sym.bit true)] } := by
          rw [p4c11e_run_succ, hstep1, p4c11e_run_zero]
        have hstep2_run : M.run 1
            { state := .finalizeScan, left := [], head := some .sep,
              right := [some (p4c11e_Sym.bit true)] } =
            { state := .accept, left := [some .sep], head := some (p4c11e_Sym.bit true),
              right := [] } := by
          rw [p4c11e_run_succ, hstep2, p4c11e_run_zero]
        have hrun : M.run 3 (M.init (([] : List Bool).map p4c11e_symEmb)) =
            { state := .accept, left := [some .sep], head := some (p4c11e_Sym.bit true),
              right := [] } := by
          rw [show (3 : ℕ) = 1 + 1 + 1 by rfl, p4c11e_run_add, p4c11e_run_add,
            hstep0_1, hstep1_run, hstep2_run]
        have hhalt : M.HaltsWithin 3 (([] : List Bool).map p4c11e_symEmb) := by
          unfold TM.HaltsWithin TM.IsHalting; rw [hrun]; left; rfl
        have hle : 3 ≤ 0 ^ K + K := by simp [K, B₀]; omega
        refine ⟨p4c11e_halts_mono M _ hle hhalt, ?_⟩
        rw [p4c11e_run_mono_output M _ hle hhalt, hrun]
        have hout := p4c11e_output_with_blanks M p4c11e_symEmb .accept [some .sep] [true] []
          (fun z hz => by simp at hz)
        have hcoe : (p4c11e_symEmb : Bool → p4c11e_Sym) = p4c11e_Sym.bit := rfl
        have huc1 : unary c = [true] := by simp [unary, hc_eq1]
        rw [huc1, hcoe]
        rw [hcoe] at hout
        dsimp only at hout ⊢
        simp only [List.map_cons, List.map_nil, Function.comp_apply, List.append_nil] at hout ⊢
        exact hout
    · have hc0 : c = 0 := by omega
      have hstep0 : M.step (M.init (([] : List Bool).map p4c11e_symEmb)) =
          { state := .accept, left := [none], head := none, right := [] } := by
        unfold TM.step TM.IsHalting M p4c11e_mulTM TM.init
        simp [hc0]
      have hrun1 : M.run 1 (M.init (([] : List Bool).map p4c11e_symEmb)) =
          { state := .accept, left := [none], head := none, right := [] } := by
        rw [p4c11e_run_succ, hstep0, p4c11e_run_zero]
      have hhalt : M.HaltsWithin 1 (([] : List Bool).map p4c11e_symEmb) := by
        unfold TM.HaltsWithin TM.IsHalting
        rw [hrun1]; left; rfl
      have hle : 1 ≤ 0 ^ K + K := by simp [K]
      refine ⟨p4c11e_halts_mono M _ hle hhalt, ?_⟩
      rw [p4c11e_run_mono_output M _ hle hhalt, hrun1]
      simp [TM.output, unary, hc0]
  · have hn_pos : 1 ≤ x.length := by omega
    cases hx_eq : x with
    | nil => simp [hx_eq] at hn
    | cons x0 xs =>
      let n : ℕ := xs.length + 1
      have hlen_n : x.length = n := by simp [hx_eq, n]
      have hscan := p4c11e_mul_scanIn a b c ha hb x0 xs
      have hstep_ft0 : M.step
          { state := .findTok ⟨0, hb⟩,
            left := List.replicate a (some .tok) ++ [some .sep] ++
              List.replicate xs.length (some .inU) ++ [some .inFirst],
            head := none, right := [] } =
          { state := .findTokScan ⟨0, hb⟩,
            left := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++
              List.replicate (0 + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
            head := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++
              List.replicate (0 + 1) (some p4c11e_Sym.sep) ++
              List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
            right := [none] } := by
        unfold TM.step TM.IsHalting M p4c11e_mulTM
        have ha_rep : List.replicate a (some p4c11e_Sym.tok) =
            some p4c11e_Sym.tok :: List.replicate (a - 1) (some p4c11e_Sym.tok) := by
          conv_lhs => rw [show a = (a - 1) + 1 by omega]
          rw [List.replicate_succ]
        simp [n, ha_rep, List.append_assoc]
      obtain ⟨steps_rnd, s', hsteps_rnd, hs', hrun_rnd⟩ :=
        p4c11e_rounds_loop a b c ha hb n (by omega) (b - 1) 0 (Nat.sub_lt hb Nat.one_pos)
      have hb_eq : (b - 1) + 1 = b := by omega
      rw [hb_eq] at hrun_rnd
      -- Finalize from `promote ⟨b - 1, _⟩`
      have hTok_pos : 1 ≤ a * n ^ b := Nat.mul_pos ha (Nat.pow_pos (by omega))
      let L_sep := List.replicate (s' + 1) (some p4c11e_Sym.sep) ++
        List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]
      have hL_sep_eq : L_sep = some p4c11e_Sym.sep ::
          (List.replicate s' (some p4c11e_Sym.sep) ++
            List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]) := by
        simp [L_sep, List.replicate_succ, List.append_assoc]
      let L_rest := List.replicate s' (some p4c11e_Sym.sep) ++
        List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]
      have hL_sep_rest : L_sep = some p4c11e_Sym.sep :: L_rest := hL_sep_eq
      have hprom_end : ∃ steps_tail L_fin R_fin blanks,
          steps_tail ≤ 2 * c + a * n ^ b + 5 ∧ (∀ z ∈ blanks, z = none) ∧
          (R_fin = List.replicate (a * n ^ b + c - 1) (some (.bit true)) ++ blanks) ∧
          M.run steps_tail
            { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
              left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
              head := none, right := [] } =
          { state := .accept, left := L_fin, head := some (.bit true), right := R_fin } := by
        by_cases hc : 0 < c
        · by_cases hc1 : 1 < c
          · have hstep_p : M.step
                { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                  left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                  head := none, right := [] } =
                { state := .appendC ⟨1, hc1⟩,
                  left := some (.bit true) :: List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                  head := none, right := [] } := by
              unfold TM.step TM.IsHalting M p4c11e_mulTM
              simp [hb_eq, hc, hc1]
            have happ := p4c11e_appendC_loop a b c ha hb (c - 1) 1 (by omega) (by omega)
              (some (.bit true)) (List.replicate (a * n ^ b) (some .tok) ++ L_sep)
            have hfin := p4c11e_finalize a b c ha hb (a * n ^ b) (c - 1) (by omega) L_rest
              [some (.bit true)] (Or.inr rfl)
            refine ⟨1 + (c - 1) + ((c - 1) + a * n ^ b + 1), some .sep :: L_rest,
              List.replicate (a * n ^ b + c - 1) (some (.bit true)), [], ?_, by simp, by simp, ?_⟩
            · omega
            · have hstep1 : M.run 1
                  { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                    left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                    head := none, right := [] } =
                  { state := .appendC ⟨1, hc1⟩,
                    left := some (.bit true) :: (List.replicate (a * n ^ b) (some .tok) ++ L_sep),
                    head := none, right := [] } := by
                rw [p4c11e_run_succ, hstep_p, p4c11e_run_zero]; rfl
              have hleft_eq :
                  List.replicate (c - 1 - 1) (some (p4c11e_Sym.bit true)) ++
                    some (p4c11e_Sym.bit true) ::
                      (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep) =
                  List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++
                    List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++
                    some p4c11e_Sym.sep :: L_rest := by
                rw [hL_sep_rest]
                have hc2 : (c - 1 - 1) + 1 = c - 1 := by omega
                rw [← hc2, List.replicate_succ']
                simp [List.append_assoc]
              have hrun12 : M.run (1 + (c - 1))
                  { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                    left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                    head := none, right := [] } =
                  { state := .finalizeScan,
                    left := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++
                      List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++
                      some p4c11e_Sym.sep :: L_rest).tail,
                    head := (List.replicate (c - 1) (some (p4c11e_Sym.bit true)) ++
                      List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++
                      some p4c11e_Sym.sep :: L_rest).headD none,
                    right := [some (p4c11e_Sym.bit true)] } := by
                rw [p4c11e_run_add, hstep1, happ, hleft_eq]
              rw [p4c11e_run_add, hrun12, hfin]
              congr 2
              have hrepl_end : List.replicate (a * n ^ b + (c - 1) - 1) (some (p4c11e_Sym.bit true)) ++
                  [some (p4c11e_Sym.bit true)] =
                  List.replicate (a * n ^ b + c - 1) (some (p4c11e_Sym.bit true)) := by
                rw [← List.replicate_succ']; congr 1; omega
              rw [hrepl_end]
          · have hc_eq1 : c = 1 := by omega
            have hstep_p : M.step
                { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                  left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                  head := none, right := [] } =
                { state := .finalizeScan,
                  left := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).tail,
                  head := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).headD none,
                  right := [some (.bit true)] } := by
              unfold TM.step TM.IsHalting M p4c11e_mulTM
              cases hLc : List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep with
              | nil => simp [L_sep] at hLc
              | cons z zs => simp [hb_eq, hc_eq1]
            have hfin := p4c11e_finalize a b c ha hb (a * n ^ b) 0 (by omega) L_rest
              [some (.bit true)] (Or.inr rfl)
            refine ⟨1 + (0 + a * n ^ b + 1), some .sep :: L_rest,
              List.replicate (a * n ^ b + c - 1) (some (.bit true)), [], ?_, by simp, by simp, ?_⟩
            · omega
            · have hstep1 : M.run 1
                  { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                    left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                    head := none, right := [] } =
                  { state := .finalizeScan,
                    left := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).tail,
                    head := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).headD none,
                    right := [some (.bit true)] } := by
                rw [p4c11e_run_succ, hstep_p, p4c11e_run_zero]
              have hsub_c1 : a * n ^ b + c - 1 = (a * n ^ b + 0 - 1) + 1 := by omega
              rw [p4c11e_run_add, hstep1, hsub_c1, List.replicate_succ']
              simp only [List.replicate_zero, List.nil_append] at hfin
              rw [hL_sep_rest]
              exact hfin
        · have hc0 : c = 0 := by omega
          have hstep_p : M.step
              { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                head := none, right := [] } =
              { state := .finalizeScan,
                left := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).tail,
                head := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).headD none,
                right := [none] } := by
            unfold TM.step TM.IsHalting M p4c11e_mulTM
            cases hLc : List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep with
            | nil => simp [L_sep] at hLc
            | cons z zs => simp [hb_eq, hc0]
          have hfin := p4c11e_finalize a b c ha hb (a * n ^ b) 0 (by omega) L_rest
            [none] (Or.inl rfl)
          have hsub_c : a * n ^ b + c - 1 = a * n ^ b + 0 - 1 := by omega
          refine ⟨1 + (0 + a * n ^ b + 1), some .sep :: L_rest,
            List.replicate (a * n ^ b + c - 1) (some (.bit true)) ++ [none], [none],
            by omega, by simp, rfl, ?_⟩
          have hstep1 : M.run 1
              { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
                left := List.replicate (a * n ^ b) (some .tok) ++ L_sep,
                head := none, right := [] } =
              { state := .finalizeScan,
                left := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).tail,
                head := (List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep).headD none,
                right := [none] } := by
            rw [p4c11e_run_succ, hstep_p, p4c11e_run_zero]
          rw [p4c11e_run_add, hstep1, hsub_c]
          simp only [List.replicate_zero, List.nil_append] at hfin
          rw [hL_sep_rest]
          exact hfin
      obtain ⟨steps_tail, L_fin, R_fin, blanks, hsteps_tail, hblanks, hR_fin, hrun_tail⟩ := hprom_end
      let total_steps : ℕ := (xs.length + 2 + a) + 1 + steps_rnd + steps_tail
      have hrun_total : M.run total_steps (M.init ((x0 :: xs).map p4c11e_symEmb)) =
          { state := .accept, left := L_fin, head := some (.bit true), right := R_fin } := by
        have hstep_ft0_run : M.run 1
            { state := .findTok ⟨0, hb⟩,
              left := List.replicate a (some .tok) ++ [some .sep] ++
                List.replicate xs.length (some .inU) ++ [some .inFirst],
              head := none, right := [] } =
            { state := .findTokScan ⟨0, hb⟩,
              left := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++
                List.replicate (0 + 1) (some p4c11e_Sym.sep) ++
                List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
              head := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++
                List.replicate (0 + 1) (some p4c11e_Sym.sep) ++
                List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
              right := [none] } := by
          rw [p4c11e_run_succ, hstep_ft0, p4c11e_run_zero]
        have hrun_rnd_m : M.run steps_rnd
            { state := .findTokScan ⟨0, hb⟩,
              left := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++
                List.replicate (0 + 1) (some p4c11e_Sym.sep) ++
                List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).tail,
              head := (List.replicate (a * n ^ 0) (some p4c11e_Sym.tok) ++
                List.replicate (0 + 1) (some p4c11e_Sym.sep) ++
                List.replicate (n - 1) (some p4c11e_Sym.inU) ++ [some p4c11e_Sym.inFirst]).headD none,
              right := [none] } =
            { state := .promote ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩,
              left := List.replicate (a * n ^ b) (some p4c11e_Sym.tok) ++ L_sep,
              head := none, right := [] } := by
          simpa [L_sep, List.append_assoc] using hrun_rnd
        rw [p4c11e_run_add, p4c11e_run_add, p4c11e_run_add, hscan, hstep_ft0_run, hrun_rnd_m, hrun_tail]
      have hhalt : M.HaltsWithin total_steps ((x0 :: xs).map p4c11e_symEmb) := by
        unfold TM.HaltsWithin TM.IsHalting
        rw [hrun_total]; left; rfl
      have hsteps_poly : total_steps ≤ n ^ K + K := by
        have hn1 : 1 ≤ n := by omega
        have h1_nb : 1 ≤ n ^ b := Nat.one_le_pow b n hn1
        have hn_nb : n ≤ n ^ b := Nat.le_self_pow (by omega) n
        have h1_nd : 1 ≤ n ^ d := Nat.one_le_pow d n hn1
        have hnb_nd : n ^ b ≤ n ^ d := Nat.pow_le_pow_right hn1 (by omega : b ≤ d)
        have hn_nd : n ≤ n ^ d := Nat.le_self_pow (by omega : d ≠ 0) n
        have hnb1 : n ^ (2 * b + 1) ≤ n ^ d := Nat.pow_le_pow_right hn1 (by omega : 2 * b + 1 ≤ d)
        have hrnd_bd : steps_rnd ≤ b * ((a * n ^ b + 1) *
            (2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10) := by
          rw [hb_eq] at hsteps_rnd
          simpa [Nat.zero_add] using hsteps_rnd
        have hpart1 : a * n ^ b + 1 ≤ (a + 1) * n ^ b := by nlinarith [h1_nb]
        have hpart2 : b * a * n ^ b + a * n ^ b + n + 30 ≤ ((b + 1) * a + 40) * n ^ b := by
          have hba : b * a * n ^ b + a * n ^ b = (b + 1) * a * n ^ b := by ring
          nlinarith [h1_nb, hn_nb]
        have hpart3 : 2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100 ≤
            (2 * ((b + 1) * a + 40) * 10 + 200) * n ^ (b + 1) := by
          have hn5 : n + 5 ≤ 10 * n := by omega
          have h1b1 : 1 ≤ n ^ (b + 1) := Nat.one_le_pow (b + 1) n hn1
          have hpow_split : n ^ b * n = n ^ (b + 1) := by rw [Nat.pow_succ]
          calc
            2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100
                ≤ 2 * (((b + 1) * a + 40) * n ^ b) * (10 * n) + 200 * n ^ (b + 1) := by
              gcongr; nlinarith [h1b1]
            _ = 2 * ((b + 1) * a + 40) * 10 * (n ^ b * n) + 200 * n ^ (b + 1) := by ring
            _ = (2 * ((b + 1) * a + 40) * 10 + 200) * n ^ (b + 1) := by rw [hpow_split]; ring
        have hnb2 : (a * n ^ b + 1) * (2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) ≤
            ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200)) * n ^ d := by
          have hpow2 : n ^ b * n ^ (b + 1) = n ^ (2 * b + 1) := by
            rw [← Nat.pow_add]; ring_nf
          calc
            (a * n ^ b + 1) * (2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100)
                ≤ ((a + 1) * n ^ b) * ((2 * ((b + 1) * a + 40) * 10 + 200) * n ^ (b + 1)) := by
              gcongr
            _ = ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200)) * (n ^ b * n ^ (b + 1)) := by ring
            _ = ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200)) * n ^ (2 * b + 1) := by rw [hpow2]
            _ ≤ ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200)) * n ^ d := by gcongr
        have hinner_add : (a * n ^ b + 1) *
            (2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10 ≤
            ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200) + 10) * n ^ d := by
          have h10 : 10 ≤ 10 * n ^ d := by nlinarith [h1_nd]
          calc
            (a * n ^ b + 1) * (2 * (b * a * n ^ b + a * n ^ b + n + 30) * (n + 5) + 100) + 10
                ≤ ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200)) * n ^ d + 10 * n ^ d :=
              Nat.add_le_add hnb2 h10
            _ = ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200) + 10) * n ^ d := by ring
        have hrnd_nd : steps_rnd ≤ b * ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200) + 10) * n ^ d :=
          (le_trans hrnd_bd (Nat.mul_le_mul_left b hinner_add)).trans_eq (by ring)
        have htail_nd : (xs.length + 2 + a) + 1 + steps_tail ≤ (2 * a + 2 * c + 100) * n ^ d := by
          have : xs.length ≤ n := by omega
          calc
            (xs.length + 2 + a) + 1 + steps_tail ≤ (n + 2 + a) + 1 + (2 * c + a * n ^ b + 5) := by
              omega
            _ ≤ n ^ d + a * n ^ d + (a + 2 * c + 8) * n ^ d := by
              have ha_nb : a * n ^ b ≤ a * n ^ d := by gcongr
              have hac : a + 2 * c + 8 ≤ (a + 2 * c + 8) * n ^ d :=
                Nat.le_mul_of_pos_right _ (by positivity)
              omega
            _ = (2 * a + 2 * c + 9) * n ^ d := by ring
            _ ≤ (2 * a + 2 * c + 100) * n ^ d := by gcongr; omega
        have hmul_poly : total_steps ≤ B₀ * n ^ d + B₀ := by
          have : total_steps ≤ B₀ * n ^ d := by
            simp only [total_steps, B₀]
            calc
              (xs.length + 2 + a) + 1 + steps_rnd + steps_tail
                  = ((xs.length + 2 + a) + 1 + steps_tail) + steps_rnd := by ring
              _ ≤ (2 * a + 2 * c + 100) * n ^ d +
                    b * ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200) + 10) * n ^ d := by
                gcongr
              _ = (b * ((a + 1) * (2 * ((b + 1) * a + 40) * 10 + 200) + 10) + 2 * a + 2 * c + 100) * n ^ d := by
                ring
          omega
        exact le_trans hmul_poly (p4c11e_poly_dom B₀ d n)
      refine ⟨?_, ?_⟩
      · simpa [hx_eq, hlen_n] using p4c11e_halts_mono M _ hsteps_poly hhalt
      · rw [show (x0 :: xs).length ^ K + K = n ^ K + K by simp [n]]
        rw [p4c11e_run_mono_output M _ hsteps_poly hhalt, hrun_total]
        have hout := p4c11e_output_with_blanks M p4c11e_symEmb .accept L_fin
          (unary (a * (x0 :: xs).length ^ b + c)) blanks hblanks
        have htot_pos : 1 ≤ a * n ^ b + c := by omega
        have hun : unary (a * (x0 :: xs).length ^ b + c) =
            true :: List.replicate (a * n ^ b + c - 1) true := by
          unfold unary
          have hn' : (x0 :: xs).length = n := by simp [n]
          rw [hn']
          conv_lhs => rw [show a * n ^ b + c = (a * n ^ b + c - 1) + 1 by omega]
          rw [List.replicate_succ]
        have hcoe : (p4c11e_symEmb : Bool → p4c11e_Sym) = p4c11e_Sym.bit := rfl
        have hfull_eq :
            List.map (some ∘ p4c11e_symEmb) (unary (a * (x0 :: xs).length ^ b + c)) ++ blanks =
              some (p4c11e_Sym.bit true) ::
                (List.replicate (a * n ^ b + c - 1) (some (p4c11e_Sym.bit true)) ++ blanks) := by
          rw [hun, hcoe]
          simp [List.map_replicate]
        dsimp only at hout ⊢
        rw [hfull_eq] at hout
        rw [hR_fin]
        exact hout

theorem p4c_1_1_ii_effpoly_core : ∀ a b c : ℕ, EffPoly (fun d => a * d ^ b + c) := by
  intro a b c
  constructor
  · refine ⟨a + b + c + 2, fun n => ?_⟩
    by_cases hb0 : b = 0
    · subst hb0
      simp only [pow_zero, mul_one]
      omega
    · by_cases hn0 : n = 0
      · subst hn0
        simp [hb0]
        omega
      · by_cases hn1 : n = 1
        · subst hn1; simp; omega
        · have hn2 : 2 ≤ n := by omega
          have ha_pow : a ≤ n ^ a := le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hn2 a)
          calc
            a * n ^ b + c ≤ n ^ a * n ^ b + (a + b + c + 2) := by
              gcongr; omega
            _ = n ^ (a + b) + (a + b + c + 2) := by rw [Nat.pow_add]
            _ ≤ n ^ (a + b + c + 2) + (a + b + c + 2) := by
              exact Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (by omega)) _
  · by_cases ha0 : a = 0
    · subst ha0
      simpa using p4c11e_constTM_spec c
    · by_cases hb0 : b = 0
      · subst hb0
        simpa using p4c11e_constTM_spec (a + c)
      · exact p4c11e_mulTM_spec a b c (by omega) (by omega)

end MulTM
end CritWinSpin

open CookPvsNP QuantumPRC CritWinSpin
set_option autoImplicit false

theorem solution : ∀ a b c : ℕ, EffPoly (fun d => a * d ^ b + c) :=
  CritWinSpin.p4c_1_1_ii_effpoly_core
