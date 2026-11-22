-- Prove2me | solution 1 for CircuitComplexity.ShannonUpper.shannon_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:41.740869+00:00
-- url     : https://prove2.me/submissions/3ac2a5a1-f2d2-426c-a19f-16b7270a8dab

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Theorems.Thm_CircuitComplexity_AONOp_eval_two_or
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace ShannonUpper
private lemma andOr2_basis_eval {n : Nat} (op : AONOp)
    (h : (Basis.andOr2.arity op).satisfiedBy n) (v : BitString n) :
    Basis.andOr2.eval op n h v = op.eval n v := rfl
private lemma treeLevel_parent (l m : Nat) (hl : 2 ≤ l) :
    treeLevel (treeParentIdx l m) = l - 1 := by
  unfold treeLevel treeParentIdx treeBase
  have h4l : 4 ≤ 2 ^ l := pow_ge_4 l hl
  have hmod : m % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
  have hlm1 : l - 1 + 1 = l := by omega
  have harg : 2 ^ (l - 1 + 1) - 4 + m % 2 ^ l + 4 = 2 ^ l + m % 2 ^ l := by
    rw [hlm1]; omega
  rw [harg]
  suffices Nat.log 2 (2 ^ l + m % 2 ^ l) = l by omega
  apply le_antisymm
  · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega)
      (show 2 ^ l + m % 2 ^ l < 2 ^ (l + 1) by have := pow_double l; omega))
  · exact Nat.le_log_of_pow_le (by omega) (by omega)
private lemma treePos_parent (l m : Nat) (_hl : 2 ≤ l) :
    treePos (treeParentIdx l m) (l - 1) = m % 2 ^ l := by
  unfold treePos treeParentIdx
  omega
private theorem testBit_sum_cond_pow_fin (k : Nat) (b : BitString k) (i : Nat) (hi : i < k) :
    Nat.testBit (Finset.sum (Finset.univ : Finset (Fin k))
      (fun j => if b j then 2^j.val else 0)) i = b ⟨i, hi⟩ := by
  -- Prove by induction on k using a helper with ∀ quantifiers
  suffices h : ∀ (kk : Nat) (bb : BitString kk) (ii : Nat) (hii : ii < kk),
    Nat.testBit (Finset.sum (Finset.univ : Finset (Fin kk))
      (fun j => if bb j then 2^j.val else 0)) ii = bb ⟨ii, hii⟩ from h k b i hi
  intro kk
  induction kk with
  | zero => intro _ ii hii; omega
  | succ n ih =>
    intro bb ii hii
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ j : Fin n,
      (if bb (Fin.castSucc j) then 2 ^ (Fin.castSucc j).val else 0) =
      (if bb (Fin.castSucc j) then 2 ^ j.val else 0) := by
      intro j; simp [Fin.val_castSucc]
    simp_rw [hcast]
    set S := Finset.sum Finset.univ
      (fun j : Fin n => if bb (Fin.castSucc j) then 2^j.val else 0)
    have hS_lt : S < 2^n := sum_cond_pow_fin_lt n (fun j => bb (Fin.castSucc j))
    by_cases hi_n : ii < n
    · -- ii < n: the last term (power 2^n) doesn't affect testBit at position ii
      by_cases hbn : bb (Fin.last n)
      · simp only [hbn, ite_true, Fin.val_last]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt (by omega)]
        exact ih (fun j => bb (Fin.castSucc j)) ii hi_n
      · simp only [hbn, Fin.val_last]
        exact ih (fun j => bb (Fin.castSucc j)) ii hi_n
    · -- ii = n
      have hii_eq : ii = n := by omega
      subst hii_eq
      have hlast_eq : (Fin.last ii : Fin (ii + 1)) = ⟨ii, hii⟩ := by ext; simp [Fin.val_last]
      by_cases hbn : bb (Fin.last ii)
      · simp only [hbn, ite_true, Fin.val_last]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hS_lt, Bool.not_false]
        rw [hlast_eq] at hbn; exact hbn.symm
      · simp only [hbn, ite_false, Fin.val_last, Nat.add_zero, Bool.false_eq_true]
        rw [Nat.testBit_lt_two_pow hS_lt]
        simp_all
private theorem lastWire_is_orChain_last (N : Nat) (hN : 16 ≤ N) :
    N + szSections (addrBits N) (dataBits N) - 1 =
    N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2) := by
  have hq2 : 2 ≤ dataBits N := dataBits_ge_two N hN
  have h4q : 4 ≤ 2 ^ dataBits N := pow_ge_4 (dataBits N) hq2
  unfold szSections oF oE oD oC; omega
private theorem colFun_at_actual_bits (N : Nat)
    (f : BitString N → Bool) (x : BitString N)
    (k q : Nat) (hkq : k + q = N) :
    let addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
    let data := shiftedBits N k q hkq x
    let aSum := Finset.sum (Finset.univ : Finset (Fin k))
      (fun j => if addr j then 2^j.val else 0)
    let dSum := Finset.sum (Finset.univ : Finset (Fin q))
      (fun j => if data j then 2^j.val else 0)
    colFun N f k q hkq
      ⟨dSum, sum_cond_pow_fin_lt q data⟩
      ⟨aSum, sum_cond_pow_fin_lt k addr⟩ = f x := by
  simp only
  unfold colFun shiftedBits
  dsimp only
  congr 1
  funext ⟨idx, hidx⟩
  dsimp only
  split_ifs with h
  · exact testBit_sum_cond_pow_fin k _ idx h
  · have hq_bound : idx - k < q := by omega
    rw [testBit_sum_cond_pow_fin q _ (idx - k) hq_bound]
    simp_all
private theorem foldl_or_all_false {n : Nat} {P : Nat → Bool}
    (hP : ∀ y, y < n → P y = false) :
    (List.range n).foldl (fun acc y => acc || P y) false = false := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (fun y hy => hP y (by omega))]
    rw [hP m (by omega)]; rfl
private theorem foldl_or_unique_true {n : Nat} {P : Nat → Bool}
    (target : Nat) (htarget : target < n)
    (hP : ∀ y, y < n → y ≠ target → P y = false) :
    (List.range n).foldl (fun acc y => acc || P y) false = P target := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases htm : target < m
    · -- target < m: result after first m was already P target
      rw [ih htm (fun y hy hne => hP y (by omega) hne)]
      rw [hP m (by omega) (by omega)]
      simp [Bool.or_false]
    · -- target = m
      have htm_eq : target = m := by omega
      subst htm_eq
      -- All terms before target are false, so foldl gives false
      rw [foldl_or_all_false (fun y hy => hP y (by omega) (by omega))]
      simp [Bool.false_or]
private theorem andLayerSem_ne (N : Nat)
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N) (hne : y ≠ dataSum N hN x) :
    andLayerSem N f hN x y hy = false := by
  unfold andLayerSem dataSum at *
  simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_and]
private theorem andLayerSem_eq (N : Nat)
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    andLayerSem N f hN x (dataSum N hN x) (dataSum_lt N hN x) = f x := by
  unfold andLayerSem dataSum
  simp only [beq_self_eq_true, Bool.true_and]
  exact colFun_at_actual_bits N f x (addrBits N) (dataBits N) (addrDataSum N hN)
private theorem or_andLayerSem_eq_f (N : Nat)
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    (List.range (2 ^ dataBits N)).foldl
      (fun acc y => acc || if h : y < 2 ^ dataBits N
        then andLayerSem N f hN x y h else false) false = f x := by
  -- Use foldl_or_unique_true with target = dataSum N hN x
  have hds_lt := dataSum_lt N hN x
  have hP_ne : ∀ y, y < 2 ^ dataBits N → y ≠ dataSum N hN x →
    (if h : y < 2 ^ dataBits N then andLayerSem N f hN x y h else false) = false := by
    intro y hy hne
    rw [dif_pos hy, andLayerSem_ne N f hN x y hy hne]
  have hfoldl := foldl_or_unique_true (dataSum N hN x) hds_lt hP_ne
  rw [hfoldl, dif_pos hds_lt, andLayerSem_eq N f hN x]
private theorem mintermTwo_eval (a b p q : Bool) :
    ((!p ^^ a) && (!q ^^ b)) = decide (a = p ∧ b = q) := by
  decide +revert
private theorem wireValue_dataLeaf (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N)
    (hyW : N + 1 + (2 ^ dataBits N - 4) + y <
          N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + 1 + (2 ^ dataBits N - 4) + y, hyW⟩ =
    (y == Finset.sum Finset.univ (fun j : Fin (dataBits N) =>
      if shiftedBits N (addrBits N) (dataBits N) (addrDataSum N hN) x j = true
      then 2 ^ j.val else 0)) := by
  have hq2 := dataBits_ge_two N hN
  have h4q := pow_ge_4 (dataBits N) hq2
  have hk3 := addrBits_ge_three N hN
  have hkq := addrDataSum N hN
  have h2q1 : 2 ^ (dataBits N + 1) = 2 * 2 ^ dataBits N := pow_double (dataBits N)
  have hsB : ∀ (j : Nat) (hj : j < 2 ^ (dataBits N + 1) - 4)
      (hjW : N + 1 + j < N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x ⟨N + 1 + j, hjW⟩ =
      decide (∀ i : Fin (treeLevel j + 1),
        x ⟨addrBits N + i.val,
          by have := i.isLt; have := treeLevel_lt j (dataBits N) hj hq2; omega⟩ =
          Nat.testBit (treePos j (treeLevel j)) i.val) := by
    intro j
    exact Nat.strongRecOn j fun j ih => by
      intro hj hjW
      rw [Circuit.wireValue_ge _ _ _ (by change ¬(N + 1 + j < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + 1 + j - N = 1 + j from by omega]
      rw [dif_neg (by omega : ¬(1 + j = 0))]
      rw [dif_pos (by unfold oC; omega : 1 + j < oC (dataBits N))]
      simp only [show 1 + j - 1 = j from by omega]
      by_cases hjL1 : j < 4
      · rw [dif_pos hjL1]
        simp only [mkG, Gate.eval, andOr2_basis_eval, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨addrBits N, _⟩ : Fin _).val < N from by
          change addrBits N < N; have := addr_le_N N hN; omega)]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨addrBits N + 1, _⟩ : Fin _).val < N from by
          change addrBits N + 1 < N; have := addr_le_N N hN; omega)]
        have htl : treeLevel j = 1 := by
          unfold treeLevel
          have h1 : Nat.log 2 (j + 4) = 2 := by
            apply le_antisymm
            · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega))
            · exact Nat.le_log_of_pow_le (by omega) (by omega)
          omega
        have htp : treePos j 1 = j := by unfold treePos treeBase; omega
        simp only [htl, htp, Nat.testBit_zero]
        have hlq : treeLevel j < dataBits N := treeLevel_lt j (dataBits N) (by omega) hq2
        have hfin_bound : ∀ (i : Fin (treeLevel j + 1)), addrBits N + i.val < N := by
          intro i; have := i.isLt; omega
        have hfin_bound2 : ∀ (i : Fin 2), addrBits N + i.val < N := by
          intro i; have := i.isLt; omega
        have hcast : (∀ (i : Fin (treeLevel j + 1)),
            x ⟨addrBits N + i.val, hfin_bound i⟩ = j.testBit i.val) ↔
            (∀ (i : Fin 2), x ⟨addrBits N + i.val, hfin_bound2 i⟩ = j.testBit i.val) := by
          constructor
          · intro h i; exact h ⟨i.val, by rw [htl]; exact i.isLt⟩
          · intro h ⟨i, hi⟩; exact h ⟨i, by rw [htl] at hi; exact hi⟩
        rw [show decide (∀ (i : Fin (treeLevel j + 1)),
              x ⟨addrBits N + ↑i, hfin_bound i⟩ = j.testBit ↑i) =
            decide (∀ (i : Fin 2),
              x ⟨addrBits N + ↑i, hfin_bound2 i⟩ = j.testBit ↑i) from
          decide_eq_decide.mpr hcast]
        simp only [Fin.forall_fin_two, Fin.val_zero, Fin.val_one,
          show addrBits N + 0 = addrBits N from by omega, Nat.testBit_zero]
        exact mintermTwo_eval _ _ _ _
      · rw [dif_neg hjL1]
        simp only [mkG, Gate.eval, andOr2_basis_eval, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        have hl2 : 2 ≤ treeLevel j := treeLevel_ge_two j (by omega)
        have hlq : treeLevel j < dataBits N := treeLevel_lt j (dataBits N) hj hq2
        have hbase : treeBase (treeLevel j) ≤ j := treeBase_le_of_level j (by omega)
        have hpi_lt : treeParentIdx (treeLevel j) (treePos j (treeLevel j)) < j :=
          treeParentIdx_lt_j _ _ j hl2 rfl hbase
        rw [Circuit.wireValue_lt _ _ _ (show (⟨addrBits N + treeLevel j, _⟩ : Fin _).val < N
          from by change addrBits N + treeLevel j < N; omega)]
        have hpar := ih (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          hpi_lt (by omega) (by omega)
        have htlp := treeLevel_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        have htlp1 : treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j))) + 1 =
          treeLevel j := by omega
        have htpp : treePos (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          (treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))) =
          treePos j (treeLevel j) % 2 ^ treeLevel j := by
          rw [htlp]; exact treePos_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        change ((false ^^ (shannonCircuit N f hN).wireValue x
            ⟨N + 1 + treeParentIdx (treeLevel j) (treePos j (treeLevel j)), by omega⟩) &&
          (!(treePos j (treeLevel j)).testBit (treeLevel j) ^^
            x ⟨addrBits N + treeLevel j, by omega⟩)) =
          decide (∀ (i : Fin (treeLevel j + 1)),
            x ⟨addrBits N + i.val, by have := i.isLt; omega⟩ =
            (treePos j (treeLevel j)).testBit i.val)
        rw [Bool.false_xor, hpar]
        rw [Bool.eq_iff_iff, Bool.and_eq_true]
        constructor
        · rintro ⟨h1, h2⟩
          rw [decide_eq_true_eq] at h1 ⊢
          intro i
          by_cases hil : i.val < treeLevel j
          · have h1i := h1 ⟨i.val, by rw [htlp1]; exact hil⟩
            rw [htpp, Nat.testBit_mod_two_pow] at h1i
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hil, Bool.true_and] at h1i
            exact Eq.mpr (by congr 1) h1i
          · have hi_eq : i.val = treeLevel j := by have := i.isLt; omega
            have h2' := (show ∀ (a b : Bool), (!b ^^ a) = true → a = b from by decide) _ _ h2
            exact Eq.mpr (by simp only [hi_eq]) h2'
        · intro h
          rw [decide_eq_true_eq] at h
          refine ⟨?_, ?_⟩
          · rw [decide_eq_true_eq]
            intro i
            rw [htpp, Nat.testBit_mod_two_pow]
            have hi : i.val < treeLevel j := by omega
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hi, Bool.true_and]
            exact Eq.mpr (by congr 1) (h ⟨i.val, by omega⟩)
          · exact (show ∀ (a b : Bool), a = b → (!b ^^ a) = true from by decide) _ _
              (Eq.mpr (by congr 1) (h ⟨treeLevel j, by omega⟩))
  specialize hsB (2 ^ dataBits N - 4 + y) (by omega) (by omega)
  simp only [show N + 1 + (2 ^ dataBits N - 4 + y) = N + 1 + (2 ^ dataBits N - 4) + y
    from by omega] at hsB
  rw [hsB]
  have htl_leaf : treeLevel (2 ^ dataBits N - 4 + y) = dataBits N - 1 := by
    unfold treeLevel
    have : Nat.log 2 (2 ^ dataBits N - 4 + y + 4) = dataBits N := by
      apply le_antisymm
      · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega))
      · exact Nat.le_log_of_pow_le (by omega) (by omega)
    omega
  have htp_leaf : treePos (2 ^ dataBits N - 4 + y) (dataBits N - 1) = y := by
    unfold treePos treeBase
    have : dataBits N - 1 + 1 = dataBits N := by omega
    rw [this]; omega
  conv_lhs => rw [show treePos (2 ^ dataBits N - 4 + y)
      (treeLevel (2 ^ dataBits N - 4 + y)) = y from by rw [htl_leaf]; exact htp_leaf]
  have hFin_eq : treeLevel (2 ^ dataBits N - 4 + y) + 1 = dataBits N := by
    rw [htl_leaf]; omega
  set data := shiftedBits N (addrBits N) (dataBits N) (addrDataSum N hN) x
  set dSum := Finset.sum Finset.univ (fun j : Fin (dataBits N) =>
    if data j then 2 ^ j.val else 0)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < dataBits N
    · rw [testBit_sum_cond_pow_fin (dataBits N) data i hi]
      exact Eq.mpr (by congr 1) (h ⟨i, by omega⟩).symm
    · have : y < 2 ^ i := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
      have : dSum < 2 ^ i := lt_of_lt_of_le
        (sum_cond_pow_fin_lt (dataBits N) data) (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow ‹y < 2 ^ i›, Nat.testBit_lt_two_pow ‹dSum < 2 ^ i›]
  · intro h
    subst h
    intro i
    have hi : i.val < dataBits N := by omega
    rw [testBit_sum_cond_pow_fin (dataBits N) data i.val hi]
    exact Eq.mpr (by congr 1) rfl
private theorem colOutput_addrLeaf (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ∀ (a : Nat) (_ha : a < 2 ^ addrBits N)
      (haW : N + oC (dataBits N) + (2 ^ addrBits N - 4) + a <
        N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oC (dataBits N) + (2 ^ addrBits N - 4) + a, haW⟩ =
      decide (a = Finset.sum Finset.univ
        (fun j : Fin (addrBits N) =>
          if x ⟨j.val, by have := j.isLt; have := addr_le_N N hN; omega⟩
          then 2 ^ j.val else 0)) := by
  intro a ha haW
  have hk3 := addrBits_ge_three N hN
  have hq2 := dataBits_ge_two N hN
  have h4k := pow_ge_4 (addrBits N) (by omega)
  have hkq := addrDataSum N hN
  set k := addrBits N
  set q := dataBits N
  set addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
  set aSum := Finset.sum Finset.univ (fun j : Fin k => if addr j then 2 ^ j.val else 0)
  have haSum_lt : aSum < 2 ^ k := sum_cond_pow_fin_lt k addr
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := pow_double k
  have hsC : ∀ (j : Nat) (hj : j < 2 ^ (k + 1) - 4)
      (hjW : N + oC q + j < N + szSections k q),
      (shannonCircuit N f hN).wireValue x ⟨N + oC q + j, hjW⟩ =
      decide (∀ i : Fin (treeLevel j + 1),
        x ⟨i.val, by have := i.isLt; have := treeLevel_lt j k hj (by omega); omega⟩ =
        Nat.testBit (treePos j (treeLevel j)) i.val) := by
    intro j
    exact Nat.strongRecOn j fun j ih => by
      intro hj hjW
      rw [Circuit.wireValue_ge _ _ _ (by change ¬(N + oC q + j < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + oC q + j - N = oC q + j from by omega]
      rw [dif_neg (by unfold oC; omega : ¬(oC q + j = 0))]
      rw [dif_neg (by unfold oC; omega : ¬(oC q + j < oC q))]
      rw [dif_pos (by unfold oD oC; omega : oC q + j < oD k q)]
      simp_rw [show oC q + j - oC (dataBits N) = j from by
        change oC q + j - oC q = j; omega]
      by_cases hjL1 : j < 4
      · rw [dif_pos hjL1]
        simp only [mkG, Gate.eval, andOr2_basis_eval, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨0, _⟩ : Fin _).val < N from by
          change 0 < N; linarith [hkq, hk3])]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨1, _⟩ : Fin _).val < N from by
          change 1 < N; linarith [hkq, hk3])]
        have htl : treeLevel j = 1 := by
          unfold treeLevel
          have : Nat.log 2 (j + 4) = 2 := le_antisymm
            (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega)))
            (Nat.le_log_of_pow_le (by omega) (by omega))
          omega
        have htp : treePos j 1 = j := by unfold treePos treeBase; omega
        have hN2 : ∀ i : Nat, i < 2 → i < N := fun i hi => by linarith [hkq, hk3]
        have hcast : (∀ i : Fin (treeLevel j + 1),
            x ⟨i.val, by have := i.isLt; have := treeLevel_lt j k hj (by omega); omega⟩ =
            j.testBit i.val) ↔
            (∀ i : Fin 2, x ⟨i.val, hN2 i.val i.isLt⟩ = j.testBit i.val) := by
          constructor
          · intro h i; exact Eq.mpr (by congr 1) (h ⟨i.val, by rw [htl]; exact i.isLt⟩)
          · intro h ⟨i, hi⟩; exact Eq.mpr (by congr 1) (h ⟨i, by rw [htl] at hi; exact hi⟩)
        conv_rhs => rw [show treePos j (treeLevel j) = j from by rw [htl]; exact htp]
        rw [decide_eq_decide.mpr hcast] <;> [skip; exact inferInstance]
        simp only [Fin.forall_fin_two, Fin.val_zero, Fin.val_one, Nat.testBit_zero]
        exact mintermTwo_eval _ _ _ _
      · rw [dif_neg hjL1]
        simp only [mkG, Gate.eval, andOr2_basis_eval, AONOp.eval,
          Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
        simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
          show ¬((1 : Nat) = 0) from by omega]
        have hl2 : 2 ≤ treeLevel j := treeLevel_ge_two j (by omega)
        have hlk : treeLevel j < k := treeLevel_lt j k hj (by omega)
        have hbase : treeBase (treeLevel j) ≤ j := treeBase_le_of_level j (by omega)
        have hpi_lt : treeParentIdx (treeLevel j) (treePos j (treeLevel j)) < j :=
          treeParentIdx_lt_j _ _ j hl2 rfl hbase
        simp only [Bool.false_xor]
        rw [Circuit.wireValue_lt _ _ _ (show (⟨treeLevel j, _⟩ : Fin _).val < N from by
          change treeLevel j < N; linarith [hkq, hlk])]
        have hpar := ih (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          hpi_lt (by omega) (by omega)
        have htlp := treeLevel_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        have htlp1 : treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j))) + 1 =
          treeLevel j := by omega
        have htpp : treePos (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))
          (treeLevel (treeParentIdx (treeLevel j) (treePos j (treeLevel j)))) =
          treePos j (treeLevel j) % 2 ^ treeLevel j := by
          rw [htlp]; exact treePos_parent (treeLevel j) (treePos j (treeLevel j)) hl2
        change ((shannonCircuit N f hN).wireValue x
            ⟨N + oC (dataBits N) + treeParentIdx (treeLevel j) (treePos j (treeLevel j)),
              by linarith [hpi_lt]⟩ &&
          (!(treePos j (treeLevel j)).testBit (treeLevel j) ^^
            x ⟨treeLevel j, by linarith [hkq, hlk]⟩)) =
          decide (∀ (i : Fin (treeLevel j + 1)),
            x ⟨i.val, by have := i.isLt; linarith [hkq, hlk]⟩ =
            (treePos j (treeLevel j)).testBit i.val)
        rw [hpar]
        rw [Bool.eq_iff_iff, Bool.and_eq_true]
        constructor
        · rintro ⟨h1, h2⟩
          rw [decide_eq_true_eq] at h1 ⊢
          intro i
          by_cases hil : i.val < treeLevel j
          · have h1i := h1 ⟨i.val, by rw [htlp1]; exact hil⟩
            rw [htpp, Nat.testBit_mod_two_pow] at h1i
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hil, Bool.true_and] at h1i
            exact Eq.mpr (by congr 1) h1i
          · have hi_eq : i.val = treeLevel j := by have := i.isLt; omega
            exact Eq.mpr (by simp only [hi_eq])
              ((show ∀ (a b : Bool), (!b ^^ a) = true → a = b from by decide) _ _ h2)
        · intro h
          rw [decide_eq_true_eq] at h
          refine ⟨?_, ?_⟩
          · rw [decide_eq_true_eq]
            intro i
            have hi : i.val < treeLevel j := by omega
            rw [htpp, Nat.testBit_mod_two_pow]
            simp only [show decide (i.val < treeLevel j) = true from
              decide_eq_true_eq.mpr hi, Bool.true_and]
            exact Eq.mpr (by congr 1) (h ⟨i.val, by omega⟩)
          · exact (show ∀ (a b : Bool), a = b → (!b ^^ a) = true from by decide) _ _
              (Eq.mpr (by congr 1) (h ⟨treeLevel j, by omega⟩))
  specialize hsC (2 ^ k - 4 + a) (by omega)
    (by omega : N + oC q + (2 ^ k - 4 + a) < N + szSections k q)
  simp only [show N + oC q + (2 ^ k - 4 + a) = N + oC q + (2 ^ k - 4) + a from by omega] at hsC
  rw [hsC]
  conv_lhs => rw [show treePos (2 ^ k - 4 + a)
      (treeLevel (2 ^ k - 4 + a)) = a from by
    rw [show treeLevel (2 ^ k - 4 + a) = k - 1 from by
      unfold treeLevel; have : Nat.log 2 (2 ^ k - 4 + a + 4) = k := le_antisymm
        (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega)))
        (Nat.le_log_of_pow_le (by omega) (by omega)); omega]
    unfold treePos treeBase; rw [show k - 1 + 1 = k from by omega]; omega]
  have hFin_eq : treeLevel (2 ^ k - 4 + a) + 1 = k := by
    have : treeLevel (2 ^ k - 4 + a) = k - 1 := by
      unfold treeLevel; have : Nat.log 2 (2 ^ k - 4 + a + 4) = k := le_antisymm
        (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) (by omega)))
        (Nat.le_log_of_pow_le (by omega) (by omega)); omega
    omega
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · rw [testBit_sum_cond_pow_fin k addr i hi]
      exact Eq.mpr (by congr 1) (h ⟨i, by omega⟩).symm
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow
            (lt_of_lt_of_le haSum_lt (Nat.pow_le_pow_right (by omega) (by omega)))]
  · intro h i
    have hlt : i.val < k := by have := i.isLt; omega
    have e : aSum.testBit i.val = addr ⟨i.val, hlt⟩ :=
      testBit_sum_cond_pow_fin k addr i.val hlt
    have key : a.testBit i.val = addr ⟨i.val, hlt⟩ :=
      (congrArg (fun n => Nat.testBit n i.val) h).trans e
    exact Eq.mpr (by congr 1) key.symm
private theorem colOutput_constFalse (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ∀ (hW : N < N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x ⟨N, hW⟩ = false := by
  intro hW
  have hk3 := addrBits_ge_three N hN
  have hkq := addrDataSum N hN
  set k := addrBits N
  set q := dataBits N
  have h0N : (0 : Nat) < N := by linarith [hkq, hk3]
  rw [Circuit.wireValue_ge _ _ _ (show ¬((⟨N, hW⟩ : Fin _).val < N) from by change ¬(N < N); omega)]
  change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
  unfold shannonGateArray
  change (shannonGateArray N f hN ⟨N - N, by omega⟩).val.eval
    ((shannonCircuit N f hN).wireValue x) = false
  unfold shannonGateArray
  rw [dif_pos (show N - N = 0 from by omega)]
  simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and]
  simp_all
private theorem wireValue_colOutput (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (y : Nat) (hy : y < 2 ^ dataBits N)
    (hyW : N + oD (addrBits N) (dataBits N) +
      colPatIdx N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩ *
        (2 ^ addrBits N - 1) + (2 ^ addrBits N - 2) <
      N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + oD (addrBits N) (dataBits N) +
        colPatIdx N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩ *
          (2 ^ addrBits N - 1) + (2 ^ addrBits N - 2), hyW⟩ =
    colFun N f (addrBits N) (dataBits N) (addrDataSum N hN) ⟨y, hy⟩
      ⟨Finset.sum Finset.univ (fun j : Fin (addrBits N) =>
        if (x ⟨j.val, by have := j.isLt; have := addr_le_N N hN; omega⟩) = true
        then 2 ^ j.val else 0),
       sum_cond_pow_fin_lt (addrBits N) (fun j =>
        x ⟨j.val, by have := j.isLt; have := addr_le_N N hN; omega⟩)⟩ := by
  have hk3 := addrBits_ge_three N hN
  have hq2 := dataBits_ge_two N hN
  have h4k := pow_ge_4 (addrBits N) (by omega)
  have hkq := addrDataSum N hN
  set k := addrBits N
  set q := dataBits N
  set p := colPatIdx N f k q hkq ⟨y, hy⟩
  set addr : BitString k := fun j => x ⟨j.val, by have := j.isLt; omega⟩
  set aSum := Finset.sum Finset.univ (fun j : Fin k => if addr j then 2 ^ j.val else 0)
  have hp_lt : p < 2 ^ (2 ^ k) := colPatIdx_lt N f k q hkq ⟨y, hy⟩
  have haSum_lt : aSum < 2 ^ k := sum_cond_pow_fin_lt k addr
  have hblk : 0 < 2 ^ k - 1 := by omega
  have hbk : (2 : Nat) ^ addrBits N = 2 ^ k := rfl
  have addrLeaf : ∀ (a : Nat) (_ha : a < 2 ^ k)
      (haW : N + oC q + (2 ^ k - 4) + a < N + szSections k q),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oC q + (2 ^ k - 4) + a, haW⟩ = decide (a = aSum) :=
    colOutput_addrLeaf N f hN x
  have constFalse_wire : ∀ (hW : N < N + szSections k q),
      (shannonCircuit N f hN).wireValue x ⟨N, hW⟩ = false :=
    colOutput_constFalse N f hN x
  have colChain : ∀ (r : Nat) (hr : r < 2 ^ k - 1)
      (hrW : N + oD k q + p * (2 ^ k - 1) + r < N + szSections k q),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oD k q + p * (2 ^ k - 1) + r, hrW⟩ =
      (List.range (r + 2)).foldl
        (fun acc a => acc || (Nat.testBit p a && decide (a = aSum))) false := by
    intro r hr hrW
    have hoE_lt : oD k q + p * (2 ^ k - 1) + (2 ^ k - 1) ≤ oE k q := by
      unfold oE
      rw [Nat.add_assoc, ← Nat.succ_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hp_lt) _
    induction r with
    | zero =>
      have h_ne0 : oD k q + p * (2 ^ k - 1) ≠ 0 := by
        change oD (addrBits N) (dataBits N) + colPatIdx N f (addrBits N) (dataBits N)
          (addrDataSum N hN)
          ⟨y, hy⟩ * (2 ^ (addrBits N) - 1) ≠ 0
        unfold oD oC; omega
      have h_ge_oC : ¬(oD k q + p * (2 ^ k - 1) < oC q) := by
        simp only [show k = addrBits N from rfl, show q = dataBits N from rfl] at *
        unfold oD oC; omega
      have h_ge_oD : ¬(oD k q + p * (2 ^ k - 1) < oD k q) := by omega
      have h_lt_oE : oD k q + p * (2 ^ k - 1) < oE k q := by linarith [hoE_lt]
      rw [Circuit.wireValue_ge _ _ _ (by
        change ¬(N + oD k q + p * (2 ^ k - 1) + 0 < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + oD k q + p * (2 ^ k - 1) + 0 - N =
        oD k q + p * (2 ^ k - 1) from by omega]
      rw [dif_neg h_ne0, dif_neg h_ge_oC, dif_neg h_ge_oD, dif_pos h_lt_oE]
      simp only [show addrBits N = k from rfl, show dataBits N = q from rfl]
      simp only [show oD k q + p * (2 ^ k - 1) - oD k q =
        p * (2 ^ k - 1) from by omega]
      simp_rw [show p * (2 ^ k - 1) % (2 ^ k - 1) = 0 from by
        rw [Nat.mul_comm]; exact Nat.mul_mod_right _ _]
      simp only [show p * (2 ^ k - 1) / (2 ^ k - 1) = p from Nat.mul_div_cancel p hblk]
      simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
        Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or]
      simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
        show ¬((1 : Nat) = 0) from by omega, Bool.false_xor,
        show (0 : Nat) + 1 = 1 from by omega]
      conv_rhs => rw [show (0 : Nat) + 2 = 2 from rfl,
        show (2 : Nat) = 1 + 1 from rfl, List.range_succ,
        show (1 : Nat) = 0 + 1 from rfl, List.range_succ, List.range_zero]
      simp only [List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.false_or]
      congr 1 <;> split_ifs with htb
      · simp only [htb, Bool.true_and]
        exact colOutput_addrLeaf N f hN x _ (hbk ▸ (show _ < 2 ^ k by omega)) _
      · simp only [Bool.eq_false_iff.mpr htb, Bool.false_and]; exact colOutput_constFalse N f hN x _
      · simp only [htb, Bool.true_and]
        exact colOutput_addrLeaf N f hN x _ (hbk ▸ (show _ < 2 ^ k by omega)) _
      · simp only [Bool.eq_false_iff.mpr htb, Bool.false_and]; exact colOutput_constFalse N f hN x _
    | succ r' ih =>
      have h_ne0' : oD k q + p * (2 ^ k - 1) + (r' + 1) ≠ 0 :=
        Nat.succ_ne_zero _
      have h_ge_oC' : ¬(oD k q + p * (2 ^ k - 1) + (r' + 1) < oC q) := by
        simp only [show k = addrBits N from rfl, show q = dataBits N from rfl] at *
        unfold oD oC; omega
      have h_ge_oD' : ¬(oD k q + p * (2 ^ k - 1) + (r' + 1) < oD k q) := by omega
      have h_lt_oE' : oD k q + p * (2 ^ k - 1) + (r' + 1) < oE k q := by linarith [hoE_lt]
      rw [Circuit.wireValue_ge _ _ _ (by
        change ¬(N + oD k q + p * (2 ^ k - 1) + (r' + 1) < N); omega)]
      change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
      unfold shannonGateArray
      simp only [show N + oD k q + p * (2 ^ k - 1) + (r' + 1) - N =
        oD k q + p * (2 ^ k - 1) + (r' + 1) from by omega]
      rw [dif_neg h_ne0', dif_neg h_ge_oC', dif_neg h_ge_oD',
        dif_pos h_lt_oE']
      simp only [show addrBits N = k from rfl, show dataBits N = q from rfl]
      simp_rw [show (oD k q + p * (2 ^ k - 1) + (r' + 1) - oD k q) =
        p * (2 ^ k - 1) + (r' + 1) from by omega]
      simp only [show (p * (2 ^ k - 1) + (r' + 1)) / (2 ^ k - 1) = p from
        Nat.div_eq_of_lt_le (by omega)
          (by simpa only [Nat.succ_mul] using Nat.add_lt_add_left hr (p * (2 ^ k - 1))),
        show (p * (2 ^ k - 1) + (r' + 1)) % (2 ^ k - 1) = r' + 1 from by
          rw [show p * (2 ^ k - 1) + (r' + 1) = (r' + 1) + (2 ^ k - 1) * p from by ring,
              Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)]
      simp only [show r' + 1 ≠ 0 from by omega, ite_false,
        show r' + 1 - 1 = r' from by omega]
      simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
        Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or]
      simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
        show ¬((1 : Nat) = 0) from by omega, Bool.false_xor,
        show r' + 1 + 1 = r' + 2 from by omega]
      conv_rhs => rw [show r' + 2 + 1 = (r' + 1) + 2 from by omega,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      congr 1
      · exact ih (by omega) (by omega)
      · split_ifs with htb2
        · simp only [htb2, Bool.true_and]
          exact colOutput_addrLeaf N f hN x _ (hbk ▸ (show _ < 2 ^ k by omega)) _
        · simp only [Bool.eq_false_iff.mpr htb2, Bool.false_and]
          exact colOutput_constFalse N f hN x _
  change (shannonCircuit N f hN).wireValue x
    ⟨N + oD k q + p * (2 ^ k - 1) + (2 ^ k - 2), by omega⟩ = _
  rw [colChain (2 ^ k - 2) (by omega) (by omega)]
  rw [show (2 ^ k - 2) + 2 = 2 ^ k from by omega]
  have hfold := foldl_or_unique_true aSum haSum_lt
    (P := fun a => Nat.testBit p a && decide (a = aSum))
    (fun a _ hne => by simp [show ¬(a = aSum) from hne])
  rw [hfold]; simp only [decide_true, Bool.and_true]
  change (colPatIdx N f k q hkq ⟨y, hy⟩).testBit aSum = _
  unfold colPatIdx
  rw [encodeCol]
  rw [testBit_sum_cond_pow_fin (2 ^ k) _ aSum haSum_lt]
private theorem wireValue_orChain_sem (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (r : Nat) (hr : r < 2 ^ dataBits N - 1)
    (hW : N + oF (addrBits N) (dataBits N) + r <
          N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + oF (addrBits N) (dataBits N) + r, hW⟩ =
    (List.range (r + 2)).foldl
      (fun acc y => acc || if h : y < 2 ^ dataBits N
        then andLayerSem N f hN x y h else false) false := by
  have andLayer_sem : ∀ (y : Nat) (hy : y < 2 ^ dataBits N)
      (hyW : N + oE (addrBits N) (dataBits N) + y <
            N + szSections (addrBits N) (dataBits N)),
      (shannonCircuit N f hN).wireValue x
        ⟨N + oE (addrBits N) (dataBits N) + y, hyW⟩ =
      andLayerSem N f hN x y hy := by
    intro y hy hyW
    rw [Circuit.wireValue_ge _ _ _ (by
      change ¬(N + oE (addrBits N) (dataBits N) + y < N); omega)]
    change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
    unfold shannonGateArray
    simp only [show N + oE (addrBits N) (dataBits N) + y - N =
      oE (addrBits N) (dataBits N) + y from by omega]
    rw [dif_neg (by
      unfold oE oD oC
      have := pow_ge_4 (dataBits N) (dataBits_ge_two N hN)
      omega :
      ¬(oE (addrBits N) (dataBits N) + y = 0))]
    rw [dif_neg (by unfold oE oD oC; omega :
      ¬(oE (addrBits N) (dataBits N) + y < oC (dataBits N)))]
    rw [dif_neg (by unfold oE oD; omega :
      ¬(oE (addrBits N) (dataBits N) + y < oD (addrBits N) (dataBits N)))]
    rw [dif_neg (by unfold oE; omega :
      ¬(oE (addrBits N) (dataBits N) + y < oE (addrBits N) (dataBits N)))]
    rw [dif_pos (by unfold oF; omega :
      oE (addrBits N) (dataBits N) + y < oF (addrBits N) (dataBits N))]
    simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
      Fin.foldl_succ_last, Fin.foldl_zero, Bool.true_and, ite_self, Bool.false_xor]
    simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
      show ¬((1 : Nat) = 0) from by omega,
      show oE (addrBits N) (dataBits N) + y - oE (addrBits N) (dataBits N) = y from by omega]
    unfold andLayerSem
    congr 1
    · exact wireValue_dataLeaf N f hN x y hy _
    · exact wireValue_colOutput N f hN x y hy _
  have hoEF : oE (addrBits N) (dataBits N) + 2 ^ dataBits N =
      oF (addrBits N) (dataBits N) := by unfold oF; ring
  have hoFsz : oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 1) =
      szSections (addrBits N) (dataBits N) := by unfold szSections oF oE oD oC; omega
  have hq2 := dataBits_ge_two N hN
  have h4q := pow_ge_4 (dataBits N) hq2
  induction r with
  | zero =>
    rw [Circuit.wireValue_ge _ _ _ (show ¬((⟨N + oF (addrBits N) (dataBits N) + 0, hW⟩ :
        Fin _).val < N) from by change ¬(N + oF (addrBits N) (dataBits N) + 0 < N); omega)]
    change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
    unfold shannonGateArray
    simp only [show N + oF (addrBits N) (dataBits N) + 0 - N =
      oF (addrBits N) (dataBits N) + 0 from by omega]
    rw [dif_neg (by unfold oF oE oD oC; omega : ¬(oF (addrBits N) (dataBits N) + 0 = 0))]
    rw [dif_neg (by unfold oF oE oD oC; omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oC (dataBits N)))]
    rw [dif_neg (by unfold oF oE oD; omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oD (addrBits N) (dataBits N)))]
    rw [dif_neg (by unfold oF oE; omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oE (addrBits N) (dataBits N)))]
    rw [dif_neg (by omega :
      ¬(oF (addrBits N) (dataBits N) + 0 < oF (addrBits N) (dataBits N)))]
    simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
      Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or, ite_self, Bool.false_xor]
    simp only [show oF (addrBits N) (dataBits N) + 0 - oF (addrBits N) (dataBits N) = 0
      from by omega, ite_true,
      Fin.val_last, Fin.val_castSucc, ite_false,
      show ¬((1 : Nat) = 0) from by omega,
      show (0 : Nat) + 1 = 1 from by omega]
    change ((shannonCircuit N f hN).wireValue x
        ⟨N + oE (addrBits N) (dataBits N) + 0, by linarith⟩ ||
      (shannonCircuit N f hN).wireValue x
        ⟨N + oE (addrBits N) (dataBits N) + 1, by linarith⟩) =
      List.foldl (fun acc y => acc || if h : y < 2 ^ dataBits N
        then andLayerSem N f hN x y h else false) false (List.range (0 + 2))
    rw [andLayer_sem 0 (by omega) (by linarith),
        andLayer_sem 1 (by omega) (by linarith)]
    simp only [show List.range (0 + 2) = [0, 1] from by decide,
      List.foldl_cons, List.foldl_nil,
      Bool.false_or, dif_pos (show 0 < 2 ^ dataBits N from by omega),
      dif_pos (show 1 < 2 ^ dataBits N from by omega)]
  | succ r' ih =>
    rw [Circuit.wireValue_ge _ _ _ (show ¬((⟨N + oF (addrBits N) (dataBits N) + (r' + 1), hW⟩ :
        Fin _).val < N) from by change ¬(N + oF (addrBits N) (dataBits N) + (r' + 1) < N); omega)]
    change (shannonGateArray N f hN ⟨_, _⟩).val.eval _ = _
    unfold shannonGateArray
    simp only [show N + oF (addrBits N) (dataBits N) + (r' + 1) - N =
      oF (addrBits N) (dataBits N) + (r' + 1) from by omega]
    rw [dif_neg (by unfold oF oE oD oC; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) = 0))]
    rw [dif_neg (by unfold oF oE oD oC; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oC (dataBits N)))]
    rw [dif_neg (by unfold oF oE oD; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oD (addrBits N) (dataBits N)))]
    rw [dif_neg (by unfold oF oE; omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oE (addrBits N) (dataBits N)))]
    rw [dif_neg (by omega :
      ¬(oF (addrBits N) (dataBits N) + (r' + 1) < oF (addrBits N) (dataBits N)))]
    simp only [mkG, Gate.eval, Basis.andOr2, AONOp.eval,
      Fin.foldl_succ_last, Fin.foldl_zero, Bool.false_or, ite_self, Bool.false_xor]
    simp only [show oF (addrBits N) (dataBits N) + (r' + 1) -
      oF (addrBits N) (dataBits N) = r' + 1 from by omega,
      show r' + 1 ≠ 0 from by omega, ite_false,
      show r' + 1 - 1 = r' from by omega]
    have hr' : r' < 2 ^ dataBits N - 1 := by omega
    have hW' : N + oF (addrBits N) (dataBits N) + r' <
        N + szSections (addrBits N) (dataBits N) := by linarith
    simp only [Fin.val_last, Fin.val_castSucc, ite_true, ite_false,
      show ¬((1 : Nat) = 0) from by omega]
    have hih := ih hr' hW'
    simp only [show r' + 1 + 1 = r' + 2 from by omega]
    change ((shannonCircuit N f hN).wireValue x ⟨N + oF (addrBits N) (dataBits N) + r', hW'⟩ ||
         (shannonCircuit N f hN).wireValue x
           ⟨N + oE (addrBits N) (dataBits N) + (r' + 2), by linarith⟩) =
        List.foldl (fun acc y => acc || if h : y < 2 ^ dataBits N
          then andLayerSem N f hN x y h else false) false (List.range (r' + 1 + 2))
    rw [hih, andLayer_sem (r' + 2) (by omega) (by linarith)]
    rw [show r' + 1 + 2 = (r' + 2) + 1 from by omega,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hr2 : r' + 2 < 2 ^ dataBits N := by omega
    rw [show andLayerSem N f hN x (r' + 2) hr2 =
      (if h : r' + 2 < 2 ^ dataBits N then andLayerSem N f hN x (r' + 2) h else false) from
      by rw [dif_pos hr2]]
    rw [Bool.or_assoc]
    simp only [show r' + 1 + 2 = r' + 2 + 1 from by omega,
      show r' + 2 = r' + 1 + 1 from by omega,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      dif_pos (show r' + 2 < 2 ^ dataBits N from by omega),
      dif_pos (show r' + 1 < 2 ^ dataBits N from by omega),
      Bool.or_assoc]
private theorem lastOrChain_eq_f (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N)
    (hW : N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2) <
          N + szSections (addrBits N) (dataBits N)) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2), hW⟩ = f x := by
  have hq2 : 2 ≤ dataBits N := dataBits_ge_two N hN
  have h4q : 4 ≤ 2 ^ dataBits N := pow_ge_4 (dataBits N) hq2
  -- Step 1: OR chain at last position = foldl of AND semantic values
  have hr : 2 ^ dataBits N - 2 < 2 ^ dataBits N - 1 := by omega
  rw [wireValue_orChain_sem N f hN x (2 ^ dataBits N - 2) hr hW]
  -- Step 2: range length (2^q - 2) + 2 = 2^q
  have hrange : (2 ^ dataBits N - 2) + 2 = 2 ^ dataBits N := by omega
  rw [hrange]
  -- Step 3: OR of all AND semantic values = f(x)
  exact or_andLayerSem_eq_f N f hN x
private theorem shannon_lastWire_correct (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    (shannonCircuit N f hN).wireValue x
      ⟨N + szSections (addrBits N) (dataBits N) - 1,
       by have := szSections_pos (addrBits N) (dataBits N); omega⟩ = f x := by
  -- Step 1: rewrite last wire index as oF k q + (2^q - 2)
  have hlast := lastWire_is_orChain_last N hN
  have hq2 : 2 ≤ dataBits N := dataBits_ge_two N hN
  have h4q : 4 ≤ 2 ^ dataBits N := pow_ge_4 (dataBits N) hq2
  have hW_or : N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2) <
    N + szSections (addrBits N) (dataBits N) := by
    unfold szSections oF oE oD oC; omega
  have hfin_eq :
    (⟨N + szSections (addrBits N) (dataBits N) - 1,
      by have := szSections_pos (addrBits N) (dataBits N); omega⟩ :
      Fin (N + szSections (addrBits N) (dataBits N))) =
    ⟨N + oF (addrBits N) (dataBits N) + (2 ^ dataBits N - 2), hW_or⟩ := by
    ext; exact hlast
  rw [hfin_eq]
  -- Step 2: that wire = f(x)
  exact lastOrChain_eq_f N f hN x hW_or
private theorem shannonCircuit_correct (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ((shannonCircuit N f hN).eval x) 0 = f x := by
  -- eval at output 0 = outputs-gate.eval(wireValue)
  simp only [Circuit.eval, shannonCircuit, Gate.eval, Basis.andOr2]
  rw [AONOp.eval_two_or]
  simp only [Bool.false_xor, Bool.or_self]
  exact shannon_lastWire_correct N f hN x
private theorem szSections_le_bound (N : Nat) (_hN : 16 ≤ N) :
    szSections (addrBits N) (dataBits N) + 1 ≤
      4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N + 2 ^ (2 ^ addrBits N + addrBits N) := by
  unfold szSections
  have hq1 : 1 ≤ 2 ^ dataBits N := Nat.one_le_two_pow
  have hk1 : 1 ≤ 2 ^ addrBits N := Nat.one_le_two_pow
  rw [show dataBits N + 1 = (dataBits N).succ from rfl, Nat.pow_succ]
  rw [show addrBits N + 1 = (addrBits N).succ from rfl, Nat.pow_succ]
  have hlib : 2 ^ (2 ^ addrBits N) * (2 ^ addrBits N - 1) ≤
      2 ^ (2 ^ addrBits N + addrBits N) := by
    calc 2 ^ (2 ^ addrBits N) * (2 ^ addrBits N - 1)
        ≤ 2 ^ (2 ^ addrBits N) * 2 ^ addrBits N := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (2 ^ addrBits N + addrBits N) := by rw [← Nat.pow_add]
  omega
end ShannonUpper
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.ShannonUpper
namespace CircuitComplexity.ShannonUpper
theorem _root_.solution (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧
      G + 1 ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) := by
  exact ⟨szSections (addrBits N) (dataBits N),
    shannonCircuit N f hN,
    funext (shannonCircuit_correct N f hN),
    szSections_le_bound N hN⟩
end CircuitComplexity.ShannonUpper
