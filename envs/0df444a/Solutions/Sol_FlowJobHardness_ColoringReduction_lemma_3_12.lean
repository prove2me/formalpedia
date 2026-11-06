-- Prove2me | solution 1 for FlowJobHardness.ColoringReduction.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:33:46.053886+00:00
-- url     : https://prove2.me/submissions/30188db4-05ef-4131-9c4e-0186fc0204e8

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace CGAux
open FlowJobHardness.ColoringReduction

theorem lexlt {a b x y m : ℕ} (hx : x < m) (hy : y < m) (h : a * m + x < b * m + y) :
    a < b ∨ (a = b ∧ x < y) := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact Or.inl h1
  · subst h1; exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have : (b + 1) * m ≤ a * m := Nat.mul_le_mul_right _ h1
    nlinarith

theorem lexeq {a b x y m : ℕ} (hx : x < m) (hy : y < m) (h : a * m + x = b * m + y) :
    a = b ∧ x = y := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exfalso
    have : (a + 1) * m ≤ b * m := Nat.mul_le_mul_right _ h1
    nlinarith
  · subst h1; exact ⟨rfl, by omega⟩
  · exfalso
    have : (b + 1) * m ≤ a * m := Nat.mul_le_mul_right _ h1
    nlinarith

theorem div_eq_iff' {x k a : ℕ} (hk : 0 < k) : x / k = a ↔ a * k ≤ x ∧ x < a * k + k := by
  constructor
  · rintro rfl
    have h1 := Nat.div_add_mod' x k
    have h2 := Nat.mod_lt x hk
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have : x / k < a + 1 := (Nat.div_lt_iff_lt_mul hk).2 (by linarith [Nat.add_mul a 1 k])
      omega
    · exact (Nat.le_div_iff_mul_le hk).2 h1

variable {n d : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d)) {r : ℕ}

theorem pos_of_fin (q : Fin (size r d n)) : 0 < n ∧ 0 < R r d := by
  have := q.isLt
  unfold size at this
  constructor
  · rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at this
    · exact h
  · rcases Nat.eq_zero_or_pos (R r d) with h | h
    · simp [h] at this
    · exact h

theorem freq_pos (v : Fin n) : 1 ≤ freq c v := by unfold freq; omega
theorem freq_le (v : Fin n) : freq c v ≤ d := by unfold freq; have := (c v).isLt; omega

theorem kl_eq (f : ℕ) (hf : f ≤ d) : r ^ (2 * f) * r ^ (2 * (d - f)) = R r d := by
  unfold R; rw [← pow_add]; congr 1; omega

theorem machVtx_val (p : Fin (size r d n)) : (machVtx p).val = p.val % n := rfl
theorem jobVtx_val (q : Fin (size r d n)) : (jobVtx q).val = q.val / R r d := rfl

theorem kpos (q : Fin (size r d n)) : 0 < r ^ (2 * jobFreq c q) := by
  have h := (pos_of_fin q).2
  rw [← kl_eq (r := r) (jobFreq c q) (freq_le c _)] at h
  exact Nat.pos_of_mul_pos_right h

theorem lpos (q : Fin (size r d n)) : 0 < r ^ (2 * (d - jobFreq c q)) := by
  have h := (pos_of_fin q).2
  rw [← kl_eq (r := r) (jobFreq c q) (freq_le c _)] at h
  exact Nat.pos_of_mul_pos_left h

theorem isLong_iff (q p : Fin (size r d n)) :
    IsLong c q p ↔ machVtx p = jobVtx q ∧
      (p.val / n) / r ^ (2 * jobFreq c q) = jobLocal q / r ^ (2 * jobFreq c q) := by
  unfold IsLong jobGroup FlowJobHardness.FlowShopGap.machGroup
  simp only [Nat.add_sub_cancel]
  rw [div_eq_iff' (kpos c q)]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by omega⟩

/-! machine keys -/

theorem key_parts (p : Fin (size r d n)) :
    d - freq c (machVtx p) < d ∧ p.val % n < n := by
  have h1 := freq_pos c (machVtx p)
  have h2 := freq_le c (machVtx p)
  exact ⟨by omega, Nat.mod_lt _ (pos_of_fin p).1⟩

theorem machKey_inj {p p' : Fin (size r d n)} (h : machKey c p = machKey c p') : p = p' := by
  unfold machKey at h
  obtain ⟨a1, b1⟩ := key_parts c p
  obtain ⟨a2, b2⟩ := key_parts c p'
  obtain ⟨h1, h2⟩ := lexeq b1 b2 h
  obtain ⟨h3, -⟩ := lexeq a1 a2 h1
  apply Fin.ext
  rw [← Nat.div_add_mod' p.val n, ← Nat.div_add_mod' p'.val n, h3, h2]

theorem machBefore_of_key_lt {p p' : Fin (size r d n)} (h : machKey c p < machKey c p') :
    MachBefore c p p' := by
  unfold machKey at h
  obtain ⟨a1, b1⟩ := key_parts c p
  obtain ⟨a2, b2⟩ := key_parts c p'
  have f1 := freq_pos c (machVtx p)
  have f2 := freq_le c (machVtx p)
  have f3 := freq_pos c (machVtx p')
  have f4 := freq_le c (machVtx p')
  unfold MachBefore FlowJobHardness.FlowShopGap.machGroup
  rcases lexlt b1 b2 h with h1 | ⟨h1, h2⟩
  · rcases lexlt a1 a2 h1 with h3 | ⟨h3, h4⟩
    · left; omega
    · right; left; exact ⟨by omega, by omega⟩
  · obtain ⟨h3, h4⟩ := lexeq a1 a2 h1
    right; right
    refine ⟨by omega, by omega, ?_⟩
    rw [Fin.lt_def, machVtx_val, machVtx_val]; exact h2

/-! the operation list -/

theorem opList_pairwise (q : Fin (size r d n)) :
    (opList c q).Pairwise (fun a b => machKey c a ≤ machKey c b) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (machKey c a ≤ machKey c b))
    (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) (jobMachines c q).toList
  unfold opList
  simpa using this

theorem opList_nodup (q : Fin (size r d n)) : (opList c q).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)

theorem mem_opList (q p : Fin (size r d n)) : p ∈ opList c q ↔ p ∈ jobMachines c q := by
  unfold opList; rw [List.mem_mergeSort, Finset.mem_toList]

theorem key_strict (q : Fin (size r d n)) {i j : Fin (opList c q).length} (h : i < j) :
    machKey c ((opList c q).get i) < machKey c ((opList c q).get j) := by
  have h1 := List.pairwise_iff_get.1 (opList_pairwise c q) i j h
  have h2 : (opList c q).get i ≠ (opList c q).get j := by
    intro e; rw [(opList_nodup c q).get_inj_iff] at e; exact absurd e (ne_of_lt h)
  rcases lt_or_eq_of_le h1 with h3 | h3
  · exact h3
  · exact absurd (machKey_inj c h3) h2

theorem key_lt_iff (q : Fin (size r d n)) {i j : Fin (opList c q).length} :
    machKey c ((opList c q).get i) < machKey c ((opList c q).get j) ↔ i < j := by
  constructor
  · intro h
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact h1
    · subst h1; omega
    · have := key_strict c q h1; omega
  · exact key_strict c q

theorem get_mem (q : Fin (size r d n)) (i : Fin (opList c q).length) :
    (opList c q).get i ∈ jobMachines c q := (mem_opList c q _).1 (List.get_mem _ _)

theorem part_a (r : ℕ) : ∀ q : Fin (size r d n), ∀ i i' : Fin ((inst G c r).μ q), i < i' →
    MachBefore c ((inst G c r).π q i) ((inst G c r).π q i') := by
  intro q i i' h
  exact machBefore_of_key_lt c (key_strict c q h)


/-! counting -/

theorem divmod_aux {m v k : ℕ} (hv : v < k) : (m * k + v) / k = m ∧ (m * k + v) % k = v := by
  have hk : 0 < k := by omega
  have h := Nat.div_add_mod' (m * k + v) k
  exact lexeq (Nat.mod_lt _ hk) hv h

theorem sum_ops {β : Type*} [AddCommMonoid β] (q : Fin (size r d n)) (f : Fin (size r d n) → β) :
    ∑ i : Fin (opList c q).length, f ((opList c q).get i) = ∑ p ∈ jobMachines c q, f p := by
  classical
  have h1 : ∑ i : Fin (opList c q).length, f ((opList c q).get i) = ((opList c q).map f).sum := by
    simp only [List.get_eq_getElem]; exact Fin.sum_univ_fun_getElem _ f
  rw [h1, ← List.sum_toFinset _ (opList_nodup c q)]
  congr 1
  ext p; simp [mem_opList]

theorem jobLocal_lt (q : Fin (size r d n)) : jobLocal q < R r d :=
  Nat.mod_lt _ (pos_of_fin q).2

theorem blk_lt (q : Fin (size r d n)) :
    jobLocal q / r ^ (2 * jobFreq c q) * r ^ (2 * jobFreq c q) + r ^ (2 * jobFreq c q) ≤ R r d := by
  have hk := kpos c q
  have hR := kl_eq (r := r) (jobFreq c q) (freq_le c _)
  have h1 : jobLocal q / r ^ (2 * jobFreq c q) < r ^ (2 * (d - jobFreq c q)) :=
    (Nat.div_lt_iff_lt_mul hk).2 (by rw [mul_comm, hR]; exact jobLocal_lt q)
  have : (jobLocal q / r ^ (2 * jobFreq c q) + 1) * r ^ (2 * jobFreq c q) ≤
      r ^ (2 * (d - jobFreq c q)) * r ^ (2 * jobFreq c q) := Nat.mul_le_mul_right _ h1
  rw [mul_comm (r ^ (2 * (d - jobFreq c q))), hR] at this
  linarith [Nat.add_mul (jobLocal q / r ^ (2 * jobFreq c q)) 1 (r ^ (2 * jobFreq c q))]

theorem card_long (q : Fin (size r d n)) [DecidablePred (IsLong c q)] :
    (Finset.univ.filter (IsLong c q)).card = r ^ (2 * jobFreq c q) := by
  obtain ⟨hn, hR⟩ := pos_of_fin q
  have hk0 : 0 < r ^ (2 * jobFreq c q) := kpos c q
  have hb0 := blk_lt c q
  have hiff := isLong_iff c q
  obtain ⟨k, hkdef⟩ : ∃ k, r ^ (2 * jobFreq c q) = k := ⟨_, rfl⟩
  rw [hkdef] at hk0 hb0 ⊢
  obtain ⟨b, hbdef⟩ : ∃ b, jobLocal q / k = b := ⟨_, rfl⟩
  rw [hbdef] at hb0
  obtain ⟨v, hvdef⟩ : ∃ v, (jobVtx q).val = v := ⟨_, rfl⟩
  have hv : v < n := hvdef ▸ (jobVtx q).isLt
  have key : ∀ p : Fin (size r d n), IsLong c q p ↔
      (p.val % n = v ∧ b * k ≤ p.val / n ∧ p.val / n < b * k + k) := by
    intro p
    rw [hiff, hkdef, hbdef, div_eq_iff' hk0, Fin.ext_iff, machVtx_val, hvdef]
  have hlt : ∀ x, x < k → (b * k + x) * n + v < size r d n := by
    intro x hx
    unfold size
    have : (b * k + x + 1) * n ≤ R r d * n := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  rw [← Finset.card_range k]
  apply Finset.card_nbij' (fun p => p.val / n - b * k)
    (fun x => ⟨((b * k + x) * n + v) % size r d n, Nat.mod_lt _ (by unfold size; positivity)⟩)
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp
    have hp' := (key p).1 hp
    simp only [Finset.coe_range, Set.mem_Iio]; omega
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    show IsLong c q _
    rw [key]
    simp only [Nat.mod_eq_of_lt (hlt x hx)]
    obtain ⟨e1, e2⟩ := divmod_aux (m := b * k + x) hv
    rw [e1, e2]; omega
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp
    have hp' := (key p).1 hp
    apply Fin.ext
    simp only
    have : b * k + (p.val / n - b * k) = p.val / n := by omega
    rw [this, ← hp'.1, Nat.div_add_mod' p.val n, Nat.mod_eq_of_lt p.isLt]
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    simp only [Nat.mod_eq_of_lt (hlt x hx)]
    rw [(divmod_aux (m := b * k + x) hv).1]; omega

theorem procTime_eq (q p : Fin (size r d n)) [Decidable (IsLong c q p)] :
    procTime c q p = if IsLong c q p then (r : ℝ) ^ (2 * (d - jobFreq c q)) else 0 := by
  unfold procTime; congr

theorem long_mem (q p : Fin (size r d n)) (h : IsLong c q p) : p ∈ jobMachines c q := by
  classical
  unfold jobMachines; simp [h]

theorem jobLength_eq (q : Fin (size r d n)) : (inst G c r).jobLength q = (R r d : ℝ) := by
  classical
  unfold Instance.jobLength
  show ∑ i : Fin (opList c q).length, procTime c q ((opList c q).get i) = _
  rw [sum_ops c q (procTime c q)]
  have : ∑ p ∈ jobMachines c q, procTime c q p = ∑ p, procTime c q p := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [procTime_eq]; split_ifs with h
    · exact absurd (long_mem c q p h) hp
    · rfl
  rw [this]
  simp only [procTime_eq]
  rw [← Finset.sum_filter, Finset.sum_const, card_long, nsmul_eq_mul]
  rw [← kl_eq (r := r) (jobFreq c q) (freq_le c _)]
  push_cast; ring


theorem jobFreq_of_long {q p : Fin (size r d n)} (h : IsLong c q p) :
    jobFreq c q = freq c (machVtx p) := by
  unfold jobFreq; rw [((isLong_iff c q p).1 h).1]

theorem card_jobs_long (p : Fin (size r d n)) [DecidablePred (fun q => IsLong c q p)] :
    (Finset.univ.filter (fun q => IsLong c q p)).card = r ^ (2 * freq c (machVtx p)) := by
  obtain ⟨hn, hR⟩ := pos_of_fin p
  have hkl := kl_eq (r := r) (freq c (machVtx p)) (freq_le c _)
  obtain ⟨u, hudef⟩ : ∃ u, (machVtx p).val = u := ⟨_, rfl⟩
  have hu : u < n := hudef ▸ (machVtx p).isLt
  have hiff : ∀ q : Fin (size r d n), IsLong c q p ↔ machVtx p = jobVtx q ∧
      (p.val / n) / r ^ (2 * freq c (machVtx p)) = jobLocal q / r ^ (2 * freq c (machVtx p)) := by
    intro q
    constructor
    · intro h
      have := (isLong_iff c q p).1 h
      rw [jobFreq_of_long c h] at this; exact this
    · intro h
      rw [isLong_iff]
      have e : jobFreq c q = freq c (machVtx p) := by unfold jobFreq; rw [h.1]
      rw [e]; exact h
  obtain ⟨k, hkdef⟩ : ∃ k, r ^ (2 * freq c (machVtx p)) = k := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l, r ^ (2 * (d - freq c (machVtx p))) = l := ⟨_, rfl⟩
  rw [hkdef, hldef] at hkl
  rw [hkdef]
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hkl; omega
    · exact h
  have hpn : p.val / n < R r d := Nat.div_lt_of_lt_mul (by have := p.isLt; unfold size at this; linarith [mul_comm n (R r d)])
  obtain ⟨b, hbdef⟩ : ∃ b, p.val / n / k = b := ⟨_, rfl⟩
  have hb0 : b * k + k ≤ R r d := by
    have h1 : b < l := by
      rw [← hbdef]; exact (Nat.div_lt_iff_lt_mul hk0).2 (by rw [mul_comm, hkl]; exact hpn)
    have : (b + 1) * k ≤ l * k := Nat.mul_le_mul_right _ h1
    rw [mul_comm l, hkl] at this; linarith [Nat.add_mul b 1 k]
  have key : ∀ q : Fin (size r d n), IsLong c q p ↔
      (q.val / R r d = u ∧ b * k ≤ q.val % R r d ∧ q.val % R r d < b * k + k) := by
    intro q
    rw [hiff, hkdef, hbdef, Fin.ext_iff, machVtx_val, jobVtx_val, eq_comm (a := b), div_eq_iff' hk0]
    unfold jobLocal
    rw [machVtx_val] at hudef
    rw [hudef, eq_comm (a := u)]
  have hlt : ∀ x, x < k → u * R r d + (b * k + x) < size r d n := by
    intro x hx
    unfold size
    have : (u + 1) * R r d ≤ n * R r d := Nat.mul_le_mul_right _ (by omega)
    rw [mul_comm (R r d) n]
    nlinarith
  rw [← Finset.card_range k]
  apply Finset.card_nbij' (fun q => q.val % R r d - b * k)
    (fun x => ⟨(u * R r d + (b * k + x)) % size r d n, Nat.mod_lt _ (by unfold size; positivity)⟩)
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hq
    have hq' := (key q).1 hq
    simp only [Finset.coe_range, Set.mem_Iio]; omega
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    show IsLong c _ p
    rw [key]
    simp only [Nat.mod_eq_of_lt (hlt x hx)]
    obtain ⟨e1, e2⟩ := divmod_aux (m := u) (k := R r d) (v := b * k + x) (by omega)
    rw [e1, e2]; omega
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hq
    have hq' := (key q).1 hq
    apply Fin.ext
    simp only
    have : b * k + (q.val % R r d - b * k) = q.val % R r d := by omega
    rw [this, ← hq'.1, mul_comm, Nat.div_add_mod q.val (R r d), Nat.mod_eq_of_lt q.isLt]
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    simp only [Nat.mod_eq_of_lt (hlt x hx)]
    rw [(divmod_aux (m := u) (k := R r d) (v := b * k + x) (by omega)).2]; omega

theorem load_eq (p : Fin (size r d n)) : (inst G c r).load p = (R r d : ℝ) := by
  classical
  unfold Instance.load
  rw [Finset.sum_filter, Fintype.sum_sigma]
  have h1 : ∀ q : Fin (size r d n),
      ∑ i : Fin ((inst G c r).μ q), (if (inst G c r).mach ⟨q, i⟩ = p then (inst G c r).proc ⟨q, i⟩ else 0)
        = procTime c q p := by
    intro q
    show ∑ i : Fin (opList c q).length,
      (fun x => if x = p then procTime c q x else 0) ((opList c q).get i) = _
    refine (sum_ops c q (fun x => if x = p then procTime c q x else 0)).trans ?_
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [procTime_eq]; split_ifs with h2
      · exact absurd (long_mem c q p h2) h
      · rfl
  rw [Finset.sum_congr rfl (fun q _ => h1 q)]
  simp only [procTime_eq]
  rw [← Finset.sum_filter]
  rw [Finset.sum_congr rfl (g := fun _ => (r : ℝ) ^ (2 * (d - freq c (machVtx p))))
    (fun q hq => by rw [jobFreq_of_long c (Finset.mem_filter.1 hq).2])]
  rw [Finset.sum_const, card_jobs_long, nsmul_eq_mul]
  rw [← kl_eq (r := r) (freq c (machVtx p)) (freq_le c _)]
  push_cast; ring


theorem card_vtx_machines (u : Fin n) :
    (Finset.univ.filter (fun p : Fin (size r d n) => machVtx p = u)).card ≤ R r d := by
  rw [← Finset.card_range (R r d)]
  apply Finset.card_le_card_of_injOn (fun p => p.val / n)
  · intro p _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.div_lt_of_lt_mul (by have := p.isLt; unfold size at this; linarith [mul_comm n (R r d)])
  · intro p hp p' hp' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp hp'
    simp only at h
    apply Fin.ext
    have e1 : p.val % n = p'.val % n := by
      rw [← machVtx_val, ← machVtx_val, hp, hp']
    rw [← Nat.div_add_mod' p.val n, ← Nat.div_add_mod' p'.val n, h, e1]

theorem mu_le (q : Fin (size r d n)) [DecidableRel G.Adj] (Δ : ℕ)
    (hΔ : ∀ v : Fin n, G.degree v ≤ Δ) : (inst G c r).μ q ≤ (Δ + 1) * R r d := by
  classical
  show (opList c q).length ≤ _
  unfold opList
  rw [List.length_mergeSort, Finset.length_toList]
  have hsub : jobMachines c q ⊆ Finset.univ.filter (IsLong c q) ∪
      (G.neighborFinset (jobVtx q)).biUnion
        (fun u => Finset.univ.filter (fun p : Fin (size r d n) => machVtx p = u)) := by
    intro p hp
    unfold jobMachines at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with h | h
    · exact Finset.mem_union_left _ (by simp [h])
    · apply Finset.mem_union_right
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨machVtx p, by simpa using h, rfl⟩
  calc (jobMachines c q).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (IsLong c q)).card + ((G.neighborFinset (jobVtx q)).biUnion
        (fun u => Finset.univ.filter (fun p : Fin (size r d n) => machVtx p = u))).card :=
          Finset.card_union_le _ _
    _ ≤ R r d + Δ * R r d := by
        apply add_le_add
        · rw [card_long]
          have := kl_eq (r := r) (jobFreq c q) (freq_le c _)
          have h2 := lpos c q
          nlinarith
        · calc _ ≤ ∑ u ∈ G.neighborFinset (jobVtx q),
                (Finset.univ.filter (fun p : Fin (size r d n) => machVtx p = u)).card :=
                  Finset.card_biUnion_le
            _ ≤ ∑ u ∈ G.neighborFinset (jobVtx q), R r d :=
                  Finset.sum_le_sum (fun u _ => card_vtx_machines u)
            _ = G.degree (jobVtx q) * R r d := by
                  rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
            _ ≤ Δ * R r d := Nat.mul_le_mul_right _ (hΔ _)
    _ = (Δ + 1) * R r d := by ring


/-! the block schedule of Claim 3.8 / Lemma 3.7 -/

open Classical in
noncomputable def cnt (q p : Fin (size r d n)) : ℕ :=
  (Finset.univ.filter (fun p' => IsLong c q p' ∧ machKey c p' < machKey c p)).card

noncomputable def sch (r : ℕ) (off : Fin n → ℕ) (o : (inst G c r).Op) : ℝ :=
  2 * (R r d : ℝ) * (off (jobVtx o.1) : ℝ) +
    ((jobLocal o.1 % r ^ (2 * jobFreq c o.1) + cnt c o.1 ((inst G c r).π o.1 o.2) : ℕ) : ℝ) *
      (r : ℝ) ^ (2 * (d - jobFreq c o.1))

theorem p_eq (q : Fin (size r d n)) (i : Fin ((inst G c r).μ q)) :
    (inst G c r).p q i = procTime c q ((inst G c r).π q i) := rfl

theorem proc_eq (o : (inst G c r).Op) :
    (inst G c r).proc o = procTime c o.1 ((inst G c r).mach o) := rfl

open Classical in
theorem cnt_mono (q : Fin (size r d n)) {p p' : Fin (size r d n)} (h : machKey c p < machKey c p') :
    cnt c q p + (if IsLong c q p then 1 else 0) ≤ cnt c q p' := by
  classical
  unfold cnt
  split_ifs with hl
  · rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter
      (fun p' => IsLong c q p' ∧ machKey c p' < machKey c p)) (a := p) (by simp)]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ⟨hl, h⟩
    · exact ⟨h1, by omega⟩
  · simp only [add_zero]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, by omega⟩

open Classical in
theorem cnt_le (q p : Fin (size r d n)) :
    cnt c q p + (if IsLong c q p then 1 else 0) ≤ r ^ (2 * jobFreq c q) := by
  classical
  rw [← card_long c q]
  unfold cnt
  split_ifs with hl
  · rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter
      (fun p' => IsLong c q p' ∧ machKey c p' < machKey c p)) (a := p) (by simp)]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, _⟩
    · exact hl
    · exact h1
  · simp only [add_zero]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1

open Classical in
theorem procTime_ite (q p : Fin (size r d n)) :
    procTime c q p = ((if IsLong c q p then 1 else 0 : ℕ) : ℝ) * (r : ℝ) ^ (2 * (d - jobFreq c q)) := by
  classical
  rw [procTime_eq]; split_ifs <;> simp

open Classical in
theorem sch_prec (off : Fin n → ℕ) (q : Fin (size r d n)) (i i' : Fin ((inst G c r).μ q))
    (h : i < i') :
    sch c r off ⟨q, i⟩ + (inst G c r).p q i ≤ sch c r off ⟨q, i'⟩ := by
  classical
  have hk : cnt c q ((inst G c r).π q i) + (if IsLong c q ((inst G c r).π q i) then 1 else 0) ≤
      cnt c q ((inst G c r).π q i') := cnt_mono c q (key_strict c q h)
  unfold sch
  rw [p_eq, procTime_ite]
  simp only
  have hl : (0 : ℝ) ≤ (r : ℝ) ^ (2 * (d - jobFreq c q)) := by positivity
  have : ((jobLocal q % r ^ (2 * jobFreq c q) + cnt c q ((inst G c r).π q i) : ℕ) : ℝ) +
      ((if IsLong c q ((inst G c r).π q i) then 1 else 0 : ℕ) : ℝ) ≤
      ((jobLocal q % r ^ (2 * jobFreq c q) + cnt c q ((inst G c r).π q i') : ℕ) : ℝ) := by
    rw [← Nat.cast_add]; exact_mod_cast (by omega)
  nlinarith

theorem sch_lo (off : Fin n → ℕ) (o : (inst G c r).Op) :
    2 * (R r d : ℝ) * (off (jobVtx o.1) : ℝ) ≤ sch c r off o := by
  unfold sch
  have : (0 : ℝ) ≤ ((jobLocal o.1 % r ^ (2 * jobFreq c o.1) + cnt c o.1 ((inst G c r).π o.1 o.2) : ℕ) : ℝ) *
      (r : ℝ) ^ (2 * (d - jobFreq c o.1)) := by positivity
  linarith

open Classical in
theorem sch_hi (off : Fin n → ℕ) (o : (inst G c r).Op) :
    sch c r off o + (inst G c r).proc o ≤ 2 * (R r d : ℝ) * ((off (jobVtx o.1) : ℝ) + 1) := by
  classical
  obtain ⟨q, i⟩ := o
  unfold sch
  rw [proc_eq, procTime_ite]
  simp only
  have h1 := cnt_le c q ((inst G c r).π q i)
  have h2 := Nat.mod_lt (jobLocal q) (kpos c q)
  have hR := kl_eq (r := r) (jobFreq c q) (freq_le c (jobVtx q))
  have hR' : (R r d : ℝ) = (r : ℝ) ^ (2 * jobFreq c q) * (r : ℝ) ^ (2 * (d - jobFreq c q)) := by
    rw [← hR]; push_cast; ring
  have hl : (0 : ℝ) ≤ (r : ℝ) ^ (2 * (d - jobFreq c q)) := by positivity
  have : ((jobLocal q % r ^ (2 * jobFreq c q) + cnt c q ((inst G c r).π q i) : ℕ) : ℝ) +
      ((if IsLong c q ((inst G c r).π q i) then 1 else 0 : ℕ) : ℝ) ≤
      2 * (r : ℝ) ^ (2 * jobFreq c q) := by
    have : jobLocal q % r ^ (2 * jobFreq c q) + cnt c q ((inst G c r).π q i) +
        (if IsLong c q ((inst G c r).π q i) then 1 else 0) ≤ 2 * r ^ (2 * jobFreq c q) := by omega
    exact_mod_cast this
  have e : (inst G c r).mach ⟨q, i⟩ = (inst G c r).π q i := rfl
  rw [e, hR']
  nlinarith [mul_le_mul_of_nonneg_right this hl]


theorem same_block {q q' p : Fin (size r d n)} (h : IsLong c q p) (h' : IsLong c q' p) :
    jobVtx q = jobVtx q' ∧ jobFreq c q = jobFreq c q' ∧ (∀ x, IsLong c q x ↔ IsLong c q' x) := by
  have a := (isLong_iff c q p).1 h
  have a' := (isLong_iff c q' p).1 h'
  have hv : jobVtx q = jobVtx q' := a.1.symm.trans a'.1
  have hf : jobFreq c q = jobFreq c q' := by unfold jobFreq; rw [hv]
  refine ⟨hv, hf, fun x => ?_⟩
  rw [← hf] at a'
  rw [isLong_iff, isLong_iff, ← hf, ← a.2, ← a'.2, hv]

theorem copy_ne {q q' p : Fin (size r d n)} (h : IsLong c q p) (h' : IsLong c q' p) (hne : q ≠ q') :
    jobLocal q % r ^ (2 * jobFreq c q) ≠ jobLocal q' % r ^ (2 * jobFreq c q') := by
  obtain ⟨hv, hf, -⟩ := same_block c h h'
  have a := (isLong_iff c q p).1 h
  have a' := (isLong_iff c q' p).1 h'
  rw [← hf] at a' ⊢
  intro e
  apply hne
  have e2 : jobLocal q = jobLocal q' := by
    rw [← Nat.div_add_mod' (jobLocal q) (r ^ (2 * jobFreq c q)),
      ← Nat.div_add_mod' (jobLocal q') (r ^ (2 * jobFreq c q)), ← a.2, ← a'.2, e]
  apply Fin.ext
  rw [← Nat.div_add_mod' q.val (R r d), ← Nat.div_add_mod' q'.val (R r d)]
  have e3 := congrArg Fin.val hv
  rw [jobVtx_val, jobVtx_val] at e3
  unfold jobLocal at e2
  rw [e3, e2]

theorem cnt_congr {q q' : Fin (size r d n)} (h : ∀ x, IsLong c q x ↔ IsLong c q' x) (p : Fin (size r d n)) :
    cnt c q p = cnt c q' p := by
  classical
  unfold cnt
  congr 1
  ext x; simp [h x]

open Classical in
theorem proc_long (o : (inst G c r).Op) (h : IsLong c o.1 ((inst G c r).mach o)) :
    (inst G c r).proc o = (r : ℝ) ^ (2 * (d - jobFreq c o.1)) := by
  rw [proc_eq, procTime_eq, if_pos h]

open Classical in
theorem proc_short (o : (inst G c r).Op) (h : ¬ IsLong c o.1 ((inst G c r).mach o)) :
    (inst G c r).proc o = 0 := by
  rw [proc_eq, procTime_eq, if_neg h]

theorem long_disj (off : Fin n → ℕ) (o o' : (inst G c r).Op) (hne : o.1 ≠ o'.1)
    (hm : (inst G c r).mach o = (inst G c r).mach o')
    (hl : IsLong c o.1 ((inst G c r).mach o)) (hl' : IsLong c o'.1 ((inst G c r).mach o')) :
    sch c r off o + (inst G c r).proc o ≤ sch c r off o' ∨
      sch c r off o' + (inst G c r).proc o' ≤ sch c r off o := by
  rw [← hm] at hl'
  obtain ⟨hv, hf, hiff⟩ := same_block c hl hl'
  have hc := copy_ne c hl hl' hne
  have hC := cnt_congr c hiff ((inst G c r).mach o)
  rw [proc_long c o hl, proc_long c o' (hm ▸ hl')]
  unfold sch
  have e1 : (inst G c r).π o.1 o.2 = (inst G c r).mach o := rfl
  have e2 : (inst G c r).π o'.1 o'.2 = (inst G c r).mach o' := rfl
  rw [e1, e2, ← hm, ← hv, ← hf, ← hC]
  rw [← hf] at hc
  have hl0 : (0 : ℝ) ≤ (r : ℝ) ^ (2 * (d - jobFreq c o.1)) := by positivity
  rcases Nat.lt_or_gt_of_ne hc with h | h
  · left
    have : ((jobLocal o.1 % r ^ (2 * jobFreq c o.1) + cnt c o.1 ((inst G c r).mach o) : ℕ) : ℝ) + 1 ≤
        ((jobLocal o'.1 % r ^ (2 * jobFreq c o.1) + cnt c o.1 ((inst G c r).mach o) : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    nlinarith [mul_le_mul_of_nonneg_right this hl0]
  · right
    have : ((jobLocal o'.1 % r ^ (2 * jobFreq c o.1) + cnt c o.1 ((inst G c r).mach o) : ℕ) : ℝ) + 1 ≤
        ((jobLocal o.1 % r ^ (2 * jobFreq c o.1) + cnt c o.1 ((inst G c r).mach o) : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    nlinarith [mul_le_mul_of_nonneg_right this hl0]

theorem mach_mem (o : (inst G c r).Op) : (inst G c r).mach o ∈ jobMachines c o.1 :=
  get_mem c o.1 o.2

theorem adj_of_short {o o' : (inst G c r).Op} (hm : (inst G c r).mach o = (inst G c r).mach o')
    (hs : ¬ IsLong c o.1 ((inst G c r).mach o)) (hl' : IsLong c o'.1 ((inst G c r).mach o')) :
    G.Adj (jobVtx o.1) (jobVtx o'.1) := by
  classical
  have h := mach_mem c o
  unfold jobMachines at h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h | h
  · exact absurd h hs
  · rw [hm, ((isLong_iff c _ _).1 hl').1] at h; exact h

theorem sch_feasible (off : Fin n → ℕ) (J : Finset (Fin (size r d n)))
    (hJ : ∀ q ∈ J, ∀ q' ∈ J, G.Adj (jobVtx q) (jobVtx q') → off (jobVtx q) ≠ off (jobVtx q')) :
    (inst G c r).IsFeasibleSchedule J (sch c r off) := by
  classical
  have hR0 : (0 : ℝ) ≤ R r d := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro o _
    have := sch_lo c off o
    have : (0 : ℝ) ≤ 2 * (R r d : ℝ) * (off (jobVtx o.1) : ℝ) := by positivity
    linarith
  · intro q _ i i' h
    exact sch_prec c off q i i' (by rw [Fin.lt_def]; omega)
  · intro o o' ho ho' hne hm
    by_cases hq : o.1 = o'.1
    · exfalso
      obtain ⟨q, i⟩ := o
      obtain ⟨q', i'⟩ := o'
      simp only at hq
      subst hq
      have : i ≠ i' := fun e => hne (by rw [e])
      exact this ((opList_nodup c q).get_inj_iff.1 hm)
    -- windows
    have window : off (jobVtx o.1) ≠ off (jobVtx o'.1) →
        sch c r off o + (inst G c r).proc o ≤ sch c r off o' ∨
          sch c r off o' + (inst G c r).proc o' ≤ sch c r off o := by
      intro hoff
      have a1 := sch_hi c off o
      have a2 := sch_hi c off o'
      have b1 := sch_lo c off o
      have b2 := sch_lo c off o'
      rcases Nat.lt_or_gt_of_ne hoff with h | h
      · left
        have : ((off (jobVtx o.1) : ℕ) : ℝ) + 1 ≤ (off (jobVtx o'.1) : ℝ) := by exact_mod_cast h
        nlinarith
      · right
        have : ((off (jobVtx o'.1) : ℕ) : ℝ) + 1 ≤ (off (jobVtx o.1) : ℝ) := by exact_mod_cast h
        nlinarith
    by_cases hl : IsLong c o.1 ((inst G c r).mach o)
    · by_cases hl' : IsLong c o'.1 ((inst G c r).mach o')
      · exact long_disj c off o o' hq hm hl hl'
      · exact window (hJ _ ho' _ ho (adj_of_short c hm.symm hl' hl)).symm
    · by_cases hl' : IsLong c o'.1 ((inst G c r).mach o')
      · exact window (hJ _ ho _ ho' (adj_of_short c hm hl hl'))
      · rw [proc_short c o hl, proc_short c o' hl']
        rcases le_total (sch c r off o) (sch c r off o') with h | h
        · left; linarith
        · right; linarith

theorem sch_makespan (off : Fin n → ℕ) (J : Finset (Fin (size r d n))) (M : ℕ)
    (hM : ∀ q ∈ J, off (jobVtx q) + 1 ≤ M) :
    (inst G c r).makespan J (sch c r off) ≤ 2 * (M : ℝ) * (R r d : ℝ) := by
  unfold Instance.makespan
  apply Real.iSup_le
  · intro o
    have := sch_hi c off o.1
    have h2 : ((off (jobVtx o.1.1) : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM _ o.2
    have : (0 : ℝ) ≤ R r d := by positivity
    nlinarith
  · positivity


/-! soundness side -/

theorem chain (s : (inst G c r).Op → ℝ) (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d n)) : ∀ m : ℕ, ∀ i j : Fin ((inst G c r).μ q), j.val = i.val + 1 + m →
      s ⟨q, i⟩ + (inst G c r).p q i ≤ s ⟨q, j⟩ := by
  intro m
  induction m with
  | zero => intro i j h; exact hs.precedence q (Finset.mem_univ _) i j (by omega)
  | succ m ih =>
    intro i j h
    have hi1 : i.val + 1 < (inst G c r).μ q := by have := j.isLt; omega
    let i1 : Fin ((inst G c r).μ q) := ⟨i.val + 1, hi1⟩
    have h1 := hs.precedence q (Finset.mem_univ _) i i1 rfl
    have h2 := ih i1 j (by simp [i1]; omega)
    have h3 := (inst G c r).p_nonneg q i1
    linarith

theorem chain' (s : (inst G c r).Op → ℝ) (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d n)) (i j : Fin ((inst G c r).μ q)) (h : i < j) :
    s ⟨q, i⟩ + (inst G c r).p q i ≤ s ⟨q, j⟩ :=
  chain c s hs q (j.val - i.val - 1) i j (by rw [Fin.lt_def] at h; omega)

theorem isLong_of_longOp {o : (inst G c r).Op} (h : IsLongOp G c r o) :
    IsLong c o.1 ((inst G c r).mach o) := by
  by_contra h'
  unfold IsLongOp at h
  rw [proc_short c o h'] at h
  exact lt_irrefl _ h

theorem key_lt_of {p p' : Fin (size r d n)}
    (h : p.val / n < p'.val / n ∨ (p.val / n = p'.val / n ∧ freq c (machVtx p') < freq c (machVtx p))) :
    machKey c p < machKey c p' := by
  unfold machKey
  obtain ⟨a1, b1⟩ := key_parts c p
  obtain ⟨a2, b2⟩ := key_parts c p'
  have f1 := freq_pos c (machVtx p)
  have f2 := freq_le c (machVtx p)
  have f3 := freq_pos c (machVtx p')
  have f4 := freq_le c (machVtx p')
  have hA : (p.val / n) * d + (d - freq c (machVtx p)) + 1 ≤ (p'.val / n) * d + (d - freq c (machVtx p')) := by
    rcases h with h | ⟨h1, h2⟩
    · have : (p.val / n + 1) * d ≤ (p'.val / n) * d := Nat.mul_le_mul_right _ h
      nlinarith
    · rw [h1]; omega
  have : ((p.val / n) * d + (d - freq c (machVtx p)) + 1) * n ≤
      ((p'.val / n) * d + (d - freq c (machVtx p'))) * n := Nat.mul_le_mul_right _ hA
  rw [Nat.add_mul, one_mul] at this
  generalize (p.val / n) * d + (d - freq c (machVtx p)) = A at this ⊢
  generalize (p'.val / n) * d + (d - freq c (machVtx p')) = A' at this ⊢
  generalize p.val % n = x at b1 ⊢
  generalize p'.val % n = y at b2 ⊢
  nlinarith

theorem mach_eq_of {p p' : Fin (size r d n)} (h1 : p.val / n = p'.val / n) (h2 : machVtx p = machVtx p') :
    p = p' := by
  apply Fin.ext
  have := congrArg Fin.val h2
  rw [machVtx_val, machVtx_val] at this
  rw [← Nat.div_add_mod' p.val n, ← Nat.div_add_mod' p'.val n, h1, this]

theorem lemma_3_11_core (hr : 2 ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (u v : Fin n) (huv : G.Adj u v) (hfreq : freq c v < freq c u)
    (L : ℝ) (g : ℕ) :
    ∀ I ∈ T G c r s L g u, ∀ J ∈ T G c r s L g v, Disjoint I J := by
  classical
  rintro I ⟨o, hgood, -, hg, hu, rfl⟩ J ⟨o', hgood', -, hg', hv, rfl⟩
  obtain ⟨hlo, i', hi', hli', hbetween, hdelay⟩ := hgood
  have hlo' := hgood'.1
  have hL := isLong_of_longOp c hlo
  have hL' := isLong_of_longOp c hlo'
  have hvq : jobVtx o.1 = u := by rw [← ((isLong_iff c _ _).1 hL).1, hu]
  have hvq' : jobVtx o'.1 = v := by rw [← ((isLong_iff c _ _).1 hL').1, hv]
  have hfq : jobFreq c o.1 = freq c u := by unfold jobFreq; rw [hvq]
  have hfq' : jobFreq c o'.1 = freq c v := by unfold jobFreq; rw [hvq']
  rw [proc_long c o hL] at hdelay
  unfold firstHalf
  rw [proc_long c o hL, proc_long c o' hL', hfq, hfq']
  rw [hfq] at hdelay
  set P : ℝ := (r : ℝ) ^ (2 * (d - freq c u)) with hP
  set P' : ℝ := (r : ℝ) ^ (2 * (d - freq c v)) with hP'
  have hP0 : 0 < P := by have : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
                         positivity
  have hPP : (r : ℝ) ^ 2 * P ≤ P' := by
    have hu1 := freq_le c u
    have e : 2 * (d - freq c v) = 2 + 2 * (d - freq c u) + 2 * (freq c u - freq c v - 1) := by omega
    rw [hP', e, pow_add, pow_add]
    have : (1 : ℝ) ≤ (r : ℝ) ^ (2 * (freq c u - freq c v - 1)) :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ r))
    have : (0 : ℝ) ≤ (r : ℝ) ^ 2 * P := by positivity
    nlinarith
  have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  -- the short operation of o.1 on the machine of o'
  have hmem : (inst G c r).mach o' ∈ jobMachines c o.1 := by
    unfold jobMachines
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    right; rw [hvq, hv]; exact huv
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 ((mem_opList c _ _).2 hmem)
  -- key comparisons
  have hk1 : machKey c ((inst G c r).mach o) < machKey c ((inst G c r).mach o') := by
    apply key_lt_of
    right
    unfold FlowJobHardness.FlowShopGap.machGroup at hg hg'
    refine ⟨by omega, ?_⟩
    rw [hu, hv]; exact hfreq
  have hmi' : machVtx ((inst G c r).π o.1 i') = u := by
    have e : (inst G c r).π o.1 i' = (inst G c r).mach ⟨o.1, i'⟩ := rfl
    rw [e, ((isLong_iff c _ _).1 (isLong_of_longOp c hli')).1]; exact hvq
  have hk2 : machKey c ((inst G c r).mach o') < machKey c ((inst G c r).π o.1 i') := by
    have hlt : machKey c ((inst G c r).mach o) < machKey c ((inst G c r).π o.1 i') :=
      key_strict c o.1 hi'
    apply key_lt_of
    left
    unfold FlowJobHardness.FlowShopGap.machGroup at hg hg'
    rcases lt_trichotomy (((inst G c r).π o.1 i').val / n) (((inst G c r).mach o).val / n) with h | h | h
    · exfalso
      have := key_lt_of c (p := (inst G c r).π o.1 i') (p' := (inst G c r).mach o) (Or.inl h)
      omega
    · exfalso
      have := mach_eq_of h (hmi'.trans hu.symm)
      rw [this] at hlt; omega
    · omega
  have hj1 : o.2 < j := by
    have := (key_lt_iff c o.1 (i := o.2) (j := j)).1 (by rw [hj]; exact hk1)
    exact this
  have hj2 : j < i' := by
    have := (key_lt_iff c o.1 (i := j) (j := i')).1 (by rw [hj]; exact hk2)
    exact this
  have c1 := chain' c s hs o.1 o.2 j hj1
  have c2 := chain' c s hs o.1 j i' hj2
  have hpj : (inst G c r).p o.1 j = 0 := by
    have : ¬ IsLong c o.1 ((inst G c r).mach ⟨o.1, j⟩) := by
      intro h
      have := ((isLong_iff c _ _).1 h).1
      have e : (inst G c r).mach ⟨o.1, j⟩ = (inst G c r).mach o' := hj
      rw [e, hv, hvq] at this
      exact G.ne_of_adj huv this.symm
    exact proc_short c ⟨o.1, j⟩ this
  have hpo : (inst G c r).p o.1 o.2 = P := by
    have := proc_long c o hL; rw [hfq] at this; exact this
  rw [hpo] at c1
  rw [hpj] at c2
  have hne : (⟨o.1, j⟩ : (inst G c r).Op) ≠ o' := by
    intro e
    have := congrArg Sigma.fst e
    simp only at this
    rw [← this, hvq] at hvq'
    exact G.ne_of_adj huv hvq'
  have hmd := hs.machine_disjoint ⟨o.1, j⟩ o' (Finset.mem_univ _) (Finset.mem_univ _) hne hj
  rw [proc_short c ⟨o.1, j⟩ (by
      intro h
      have := ((isLong_iff c _ _).1 h).1
      have e : (inst G c r).mach ⟨o.1, j⟩ = (inst G c r).mach o' := hj
      rw [e, hv, hvq] at this
      exact G.ne_of_adj huv this.symm),
    proc_long c o' hL', hfq'] at hmd
  rw [Set.Ico_disjoint_Ico]
  by_contra hcon
  push_neg at hcon
  have hc1 : s o < s o' + P' / 2 := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hcon (min_le_right _ _))
  have hc2 : s o' < s o + P / 2 := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hcon (min_le_left _ _))
  rcases hmd with h | h
  · linarith
  · nlinarith


/-! Lemma 3.10 -/

open Classical in
noncomputable def Ls (r : ℕ) (q : Fin (size r d n)) : Finset (Fin ((inst G c r).μ q)) :=
  Finset.univ.filter (fun i => IsLongOp G c r ⟨q, i⟩)

open Classical in
noncomputable def nxt (r : ℕ) (q : Fin (size r d n)) (a : Fin ((inst G c r).μ q)) :
    Fin ((inst G c r).μ q) :=
  if h : ((Ls c r q).filter (fun b => a < b)).Nonempty then ((Ls c r q).filter (fun b => a < b)).min' h
  else a

theorem nxt_spec (q : Fin (size r d n)) (a b : Fin ((inst G c r).μ q)) (hb : b ∈ Ls c r q)
    (hab : a < b) (hmin : ∀ x ∈ Ls c r q, a < x → b ≤ x) : nxt c r q a = b := by
  classical
  have hne : ((Ls c r q).filter (fun b => a < b)).Nonempty := ⟨b, by simp [hab, hb]⟩
  unfold nxt
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simp [hab, hb])
  · apply Finset.le_min'
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact hmin x hx.1 hx.2

theorem nxt_mem (q : Fin (size r d n)) (a b : Fin ((inst G c r).μ q)) (hb : b ∈ Ls c r q)
    (hab : a < b) : nxt c r q a ∈ Ls c r q ∧ a < nxt c r q a ∧
      ∀ x ∈ Ls c r q, a < x → x < nxt c r q a → False := by
  classical
  have hne : ((Ls c r q).filter (fun b => a < b)).Nonempty := ⟨b, by simp [hab, hb]⟩
  unfold nxt
  rw [dif_pos hne]
  have hm := Finset.min'_mem _ hne
  simp only [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2, fun x hx hax hlt => ?_⟩
  have := Finset.min'_le ((Ls c r q).filter (fun b => a < b)) x (by simp [hx, hax])
  exact absurd hlt (not_lt.2 this)

theorem telescope (s : (inst G c r).Op → ℝ) (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d n)) : ∀ j : Fin ((inst G c r).μ q), j ∈ Ls c r q →
      ∑ a ∈ (Ls c r q).filter (fun a => a < j), (s ⟨q, nxt c r q a⟩ - s ⟨q, a⟩) ≤ s ⟨q, j⟩ := by
  classical
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    intro hj
    by_cases hA : ((Ls c r q).filter (fun a => a < j)).Nonempty
    · set j' := ((Ls c r q).filter (fun a => a < j)).max' hA with hj'
      have hj'm := Finset.max'_mem _ hA
      rw [← hj'] at hj'm
      simp only [Finset.mem_filter] at hj'm
      have hsplit : (Ls c r q).filter (fun a => a < j) =
          insert j' ((Ls c r q).filter (fun a => a < j')) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hxj⟩
          by_cases e : x = j'
          · left; exact e
          · right
            refine ⟨hx, lt_of_le_of_ne ?_ e⟩
            exact Finset.le_max' _ x (by simp [hx, hxj])
        · rintro (rfl | ⟨hx, hxj⟩)
          · exact hj'm
          · exact ⟨hx, lt_trans hxj hj'm.2⟩
      rw [hsplit, Finset.sum_insert (by simp)]
      have hn : nxt c r q j' = j := by
        apply nxt_spec c q j' j hj hj'm.2
        intro x hx hjx
        by_contra hxj
        push_neg at hxj
        have := Finset.le_max' ((Ls c r q).filter (fun a => a < j)) x (by simp [hx, hxj])
        rw [← hj'] at this
        exact absurd hjx (not_lt.2 this)
      rw [hn]
      have := ih j' hj'm.2 hj'm.1
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hA, Finset.sum_empty]
      exact hs.start_nonneg _ (Finset.mem_univ _)

theorem longOp_iff (hr : 1 ≤ r) (o : (inst G c r).Op) :
    IsLongOp G c r o ↔ IsLong c o.1 ((inst G c r).mach o) := by
  constructor
  · exact isLong_of_longOp c
  · intro h
    unfold IsLongOp
    rw [proc_long c o h]
    have : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    positivity

theorem card_Ls (hr : 1 ≤ r) (q : Fin (size r d n)) : (Ls c r q).card = r ^ (2 * jobFreq c q) := by
  classical
  rw [← card_long c q]
  unfold Ls
  rw [Finset.card_filter, Finset.card_filter]
  have h1 : ∀ i : Fin ((inst G c r).μ q),
      (if IsLongOp G c r ⟨q, i⟩ then 1 else 0) =
        (fun p => if IsLong c q p then 1 else 0) ((opList c q).get i) := by
    intro i
    simp only
    rw [if_congr (longOp_iff c hr ⟨q, i⟩) rfl rfl]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  refine (sum_ops c q (fun p => if IsLong c q p then 1 else 0)).trans ?_
  rw [← Finset.card_filter, ← Finset.card_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨long_mem c q p h, h⟩⟩

theorem lemma_3_10_core (hr : 1 ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d n)) (hq : jobCompletion G c r s q ≤ (r : ℝ) * (R r d : ℝ)) :
    (1 - 4 / (r : ℝ)) * (r : ℝ) ^ (2 * jobFreq c q) ≤ (goodCount G c r s q : ℝ) := by
  classical
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  set k := r ^ (2 * jobFreq c q) with hk
  set ℓ : ℝ := (r : ℝ) ^ (2 * (d - jobFreq c q)) with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  have hR : (R r d : ℝ) = (k : ℝ) * ℓ := by
    rw [hℓ, hk, ← kl_eq (r := r) (jobFreq c q) (freq_le c _)]; push_cast; ring
  have hkr : (r : ℝ) ^ 2 ≤ (k : ℝ) := by
    have hf := freq_pos c (jobVtx q)
    have : r ^ 2 ≤ k := by
      rw [hk]; apply Nat.pow_le_pow_right (by omega); unfold jobFreq; omega
    exact_mod_cast this
  have hcard := card_Ls c hr q
  have hk1 : 1 ≤ k := by have := kpos c q; omega
  have hLne : (Ls c r q).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  set last := (Ls c r q).max' hLne with hlast
  have hlastm : last ∈ Ls c r q := Finset.max'_mem _ _
  have proc_of : ∀ a ∈ Ls c r q, (inst G c r).p q a = ℓ := by
    intro a ha
    unfold Ls at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact proc_long c ⟨q, a⟩ (isLong_of_longOp c ha)
  -- completion bound
  have hcomp : s ⟨q, last⟩ + ℓ ≤ jobCompletion G c r s q := by
    rw [← proc_of last hlastm]
    unfold jobCompletion
    exact le_ciSup (f := fun i : Fin ((inst G c r).μ q) => s ⟨q, i⟩ + (inst G c r).p q i)
      (Set.finite_range _).bddAbove last
  have htel := telescope c s hs q last hlastm
  set A := (Ls c r q).filter (fun a => a < last) with hA
  have hAcard : A.card = k - 1 := by
    have : A = (Ls c r q).erase last := by
      ext x
      simp only [hA, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hx, hxl⟩; exact ⟨ne_of_lt hxl, hx⟩
      · rintro ⟨hne, hx⟩; exact ⟨hx, lt_of_le_of_ne (Finset.le_max' _ x hx) hne⟩
    rw [this, Finset.card_erase_of_mem hlastm, hcard]
  -- good operations
  have good_long : ∀ i, IsGood G c r s ⟨q, i⟩ → i ∈ A := by
    intro i hg
    obtain ⟨hl, i', hi', hli', -, -⟩ := hg
    have hiL : i ∈ Ls c r q := by unfold Ls; simpa using hl
    have hi'L : i' ∈ Ls c r q := by unfold Ls; simpa using hli'
    simp only [hA, Finset.mem_filter]
    exact ⟨hiL, lt_of_lt_of_le hi' (Finset.le_max' _ i' hi'L)⟩
  have hGcount : (goodCount G c r s q : ℝ) =
      ∑ a ∈ A, (if IsGood G c r s ⟨q, a⟩ then (1 : ℝ) else 0) := by
    unfold goodCount
    rw [Finset.sum_boole]
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨good_long i h, h⟩, fun h => h.2⟩
  have hgap : ∀ a ∈ A, ℓ + (r : ℝ) ^ 2 / 4 * ℓ * (1 - (if IsGood G c r s ⟨q, a⟩ then (1 : ℝ) else 0))
      ≤ s ⟨q, nxt c r q a⟩ - s ⟨q, a⟩ := by
    intro a ha
    simp only [hA, Finset.mem_filter] at ha
    obtain ⟨hnL, hlt, hbet⟩ := nxt_mem c q a last hlastm ha.2
    have hch := chain' c s hs q a (nxt c r q a) hlt
    rw [proc_of a ha.1] at hch
    split_ifs with hg
    · linarith
    · -- not good: the delay is large
      by_contra hcon
      push_neg at hcon
      apply hg
      have haL := ha.1
      unfold Ls at haL hnL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at haL hnL
      refine ⟨haL, nxt c r q a, hlt, hnL, ?_, ?_⟩
      · intro x hx1 hx2 hxl
        exact hbet x (by unfold Ls; simpa using hxl) hx1 hx2
      · have e : (inst G c r).proc ⟨q, a⟩ = ℓ := proc_of a ha.1
        simp only
        rw [e]
        linarith
  have hsum := Finset.sum_le_sum hgap
  rw [Finset.sum_add_distrib, Finset.sum_const] at hsum
  have hsum2 : ∑ a ∈ A, (r : ℝ) ^ 2 / 4 * ℓ * (1 - (if IsGood G c r s ⟨q, a⟩ then (1 : ℝ) else 0)) =
      (r : ℝ) ^ 2 / 4 * ℓ * ((A.card : ℝ) - goodCount G c r s q) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hGcount]; simp
  rw [hsum2, nsmul_eq_mul, hAcard] at hsum
  have hk1r : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
  rw [hk1r] at hsum
  -- combine
  have key : (k : ℝ) * ℓ + (r : ℝ) ^ 2 / 4 * ℓ * ((k : ℝ) - 1 - goodCount G c r s q) ≤
      (r : ℝ) * ((k : ℝ) * ℓ) := by
    rw [← hR]; nlinarith
  have key2 : (k : ℝ) + (r : ℝ) ^ 2 / 4 * ((k : ℝ) - 1 - goodCount G c r s q) ≤ (r : ℝ) * k := by
    have : ((k : ℝ) + (r : ℝ) ^ 2 / 4 * ((k : ℝ) - 1 - goodCount G c r s q)) * ℓ ≤ ((r : ℝ) * k) * ℓ := by
      nlinarith
    exact le_of_mul_le_mul_right this hℓ0
  have hkc : (r : ℝ) ^ (2 * jobFreq c q) = (k : ℝ) := by rw [hk]; push_cast; ring
  rw [hkc]
  rw [show (1 - 4 / (r : ℝ)) * (k : ℝ) = (k : ℝ) - 4 * k / r by ring]
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hrpos]
  by_contra hcon
  push_neg at hcon
  -- hcon : (k - G) * r < 4k
  nlinarith


/-! Lemma 3.12 -/

open Classical in
noncomputable def Ogv (r : ℕ) (s : (inst G c r).Op → ℝ) (L : ℝ) (g : ℕ) (v : Fin n) :
    Finset (inst G c r).Op :=
  Finset.univ.filter (fun o => IsGood G c r s o ∧
      jobCompletion G c r s o.1 ≤ L * (R r d : ℝ) ∧
      FlowJobHardness.FlowShopGap.machGroup n ((inst G c r).mach o).val = g ∧
      machVtx ((inst G c r).mach o) = v)

theorem covered_eq (s : (inst G c r).Op → ℝ) (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (L : ℝ) (g : ℕ) (v : Fin n) :
    coveredLength G c r s L g v = ∑ o ∈ Ogv c r s L g v, (inst G c r).proc o / 2 := by
  classical
  have hU : ⋃₀ T G c r s L g v = ⋃ o ∈ Ogv c r s L g v, firstHalf G c r s o := by
    ext t
    simp only [Set.mem_sUnion, Set.mem_iUnion, T, Set.mem_setOf_eq, Ogv, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨I, ⟨o, h1, h2, h3, h4, rfl⟩, ht⟩; exact ⟨o, ⟨h1, h2, h3, h4⟩, ht⟩
    · rintro ⟨o, ⟨h1, h2, h3, h4⟩, ht⟩; exact ⟨_, ⟨o, h1, h2, h3, h4, rfl⟩, ht⟩
  unfold coveredLength
  rw [hU, MeasureTheory.measure_biUnion_finset]
  · rw [ENNReal.toReal_sum (fun o _ => by unfold firstHalf; rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro o _
    unfold firstHalf
    have hp : (0 : ℝ) ≤ (inst G c r).proc o := (inst G c r).p_nonneg o.1 o.2
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    ring
  · intro o ho o' ho' hne
    simp only [Ogv, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ho ho'
    have hm : (inst G c r).mach o = (inst G c r).mach o' := by
      apply mach_eq_of
      · have h1 := ho.2.2.1; have h2 := ho'.2.2.1
        unfold FlowJobHardness.FlowShopGap.machGroup at h1 h2; omega
      · rw [ho.2.2.2, ho'.2.2.2]
    have hd := hs.machine_disjoint o o' (Finset.mem_univ _) (Finset.mem_univ _) hne hm
    have p1 := (inst G c r).p_nonneg o.1 o.2
    have p2 := (inst G c r).p_nonneg o'.1 o'.2
    have e1 : (inst G c r).proc o = (inst G c r).p o.1 o.2 := rfl
    have e2 : (inst G c r).proc o' = (inst G c r).p o'.1 o'.2 := rfl
    unfold firstHalf
    rw [Function.onFun, Set.Ico_disjoint_Ico]
    rcases hd with h | h
    · calc min (s o + (inst G c r).proc o / 2) (s o' + (inst G c r).proc o' / 2)
          ≤ s o + (inst G c r).proc o / 2 := min_le_left _ _
        _ ≤ s o' := by linarith
        _ ≤ max (s o) (s o') := le_max_right _ _
    · calc min (s o + (inst G c r).proc o / 2) (s o' + (inst G c r).proc o' / 2)
          ≤ s o' + (inst G c r).proc o' / 2 := min_le_right _ _
        _ ≤ s o := by linarith
        _ ≤ max (s o) (s o') := le_max_left _ _
  · intro o _; exact measurableSet_Ico

theorem lemma_3_12_core (hr : 8 ≤ r) (L : ℝ) (hL0 : 0 < L) (hLr : L ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (hhalf : (size r d n : ℝ) ≤ 2 * (finishedCount G c r s L : ℝ)) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ R r d ∧
      (R r d : ℝ) * n / 8 ≤ ∑ v : Fin n, coveredLength G c r s L g v := by
  classical
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hR1 : 1 ≤ R r d := by unfold R; exact Nat.one_le_pow _ _ (by omega)
  set C : (inst G c r).Op → Prop := fun o => IsGood G c r s o ∧
      jobCompletion G c r s o.1 ≤ L * (R r d : ℝ) with hC
  set f : (inst G c r).Op → ℝ := fun o => (inst G c r).proc o / 2 with hf
  set grp : (inst G c r).Op → ℕ := fun o =>
    FlowJobHardness.FlowShopGap.machGroup n ((inst G c r).mach o).val with hgrp
  -- total over groups
  have htot : ∑ g ∈ Finset.Icc 1 (R r d), ∑ v : Fin n, coveredLength G c r s L g v =
      ∑ o ∈ Finset.univ.filter C, f o := by
    have h1 : ∀ g, ∑ v : Fin n, coveredLength G c r s L g v =
        ∑ o ∈ (Finset.univ.filter C).filter (fun o => grp o = g), f o := by
      intro g
      simp only [covered_eq c s hs]
      rw [← Finset.sum_fiberwise ((Finset.univ.filter C).filter (fun o => grp o = g))
        (fun o => machVtx ((inst G c r).mach o)) f]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext o
      simp only [Ogv, Finset.mem_filter, Finset.mem_univ, true_and, hC, hgrp]
      tauto
    simp only [h1]
    apply Finset.sum_fiberwise_of_maps_to
    intro o _
    rw [Finset.mem_Icc]
    show 1 ≤ ((inst G c r).mach o).val / n + 1 ∧ ((inst G c r).mach o).val / n + 1 ≤ R r d
    have hlt : ((inst G c r).mach o).val < R r d * n := ((inst G c r).mach o).isLt
    have : ((inst G c r).mach o).val / n < R r d :=
      Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt)
    exact ⟨Nat.le_add_left _ _, Nat.succ_le_of_lt this⟩
  -- lower bound on the total
  have hjob : ∀ q : Fin (size r d n), jobCompletion G c r s q ≤ L * (R r d : ℝ) →
      (R r d : ℝ) / 4 ≤ ∑ i : Fin ((inst G c r).μ q),
        (if IsGood G c r s ⟨q, i⟩ then (inst G c r).proc ⟨q, i⟩ / 2 else 0) := by
    intro q hq
    have h310 := lemma_3_10_core c (by omega) s hs q (by
      have : (0 : ℝ) ≤ R r d := by positivity
      nlinarith)
    have e : ∀ i : Fin ((inst G c r).μ q),
        (if IsGood G c r s ⟨q, i⟩ then (inst G c r).proc ⟨q, i⟩ / 2 else 0) =
          (if IsGood G c r s ⟨q, i⟩ then (r : ℝ) ^ (2 * (d - jobFreq c q)) / 2 else 0) := by
      intro i
      split_ifs with h
      · rw [proc_long c ⟨q, i⟩ (isLong_of_longOp c h.1)]
      · rfl
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have hgc : ((Finset.univ.filter fun i : Fin ((inst G c r).μ q) => IsGood G c r s ⟨q, i⟩).card : ℝ)
        = goodCount G c r s q := by unfold goodCount; rfl
    rw [hgc]
    have hR : (R r d : ℝ) = (r : ℝ) ^ (2 * jobFreq c q) * (r : ℝ) ^ (2 * (d - jobFreq c q)) := by
      rw [← kl_eq (r := r) (jobFreq c q) (freq_le c _)]; push_cast; ring
    have hl : (0 : ℝ) < (r : ℝ) ^ (2 * (d - jobFreq c q)) := by positivity
    have hk : (0 : ℝ) ≤ (r : ℝ) ^ (2 * jobFreq c q) := by positivity
    have h48 : (1 : ℝ) / 2 ≤ 1 - 4 / (r : ℝ) := by
      have : (4 : ℝ) / r ≤ 1 / 2 := by
        rw [div_le_iff₀ hrpos]; have : (8 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      linarith
    rw [hR]
    have : (1 : ℝ) / 2 * (r : ℝ) ^ (2 * jobFreq c q) ≤ goodCount G c r s q := by nlinarith
    nlinarith
  have hsum_ops : ∑ o ∈ Finset.univ.filter C, f o =
      ∑ q ∈ Finset.univ.filter (fun q : Fin (size r d n) => jobCompletion G c r s q ≤ L * (R r d : ℝ)),
        ∑ i : Fin ((inst G c r).μ q),
          (if IsGood G c r s ⟨q, i⟩ then (inst G c r).proc ⟨q, i⟩ / 2 else 0) := by
    rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs with hq
    · apply Finset.sum_congr rfl
      intro i _
      simp only [hC, hf, hq, and_true]
    · apply Finset.sum_eq_zero
      intro i _
      simp only [hC, hq, and_false, if_false]
  have hlow : (R r d : ℝ) * ((R r d : ℝ) * n / 8) ≤ ∑ o ∈ Finset.univ.filter C, f o := by
    rw [hsum_ops]
    have := Finset.card_nsmul_le_sum (Finset.univ.filter (fun q : Fin (size r d n) =>
        jobCompletion G c r s q ≤ L * (R r d : ℝ))) _ ((R r d : ℝ) / 4)
      (fun q hq => hjob q (Finset.mem_filter.1 hq).2)
    rw [nsmul_eq_mul] at this
    have hfc : (finishedCount G c r s L : ℝ) = ((Finset.univ.filter (fun q : Fin (size r d n) =>
        jobCompletion G c r s q ≤ L * (R r d : ℝ))).card : ℝ) := by unfold finishedCount; rfl
    rw [← hfc] at this
    have hsz : (size r d n : ℝ) = (R r d : ℝ) * n := by unfold size; push_cast; ring
    have hR0 : (0 : ℝ) ≤ R r d := by positivity
    nlinarith
  rw [← htot] at hlow
  have hne : (Finset.Icc 1 (R r d)).Nonempty := ⟨1, by simp [hR1]⟩
  have hconst : ∑ g ∈ Finset.Icc 1 (R r d), ((R r d : ℝ) * n / 8) =
      (R r d : ℝ) * ((R r d : ℝ) * n / 8) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  rw [← hconst] at hlow
  obtain ⟨g, hg, hle⟩ := Finset.exists_le_of_sum_le hne hlow
  rw [Finset.mem_Icc] at hg
  exact ⟨g, hg.1, hg.2, hle⟩

end CGAux

open FlowJobHardness.ColoringReduction in
theorem solution {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (hr : 8 ≤ r) (L : ℝ) (hL0 : 0 < L) (hLr : L ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (hhalf : (size r d n : ℝ) ≤ 2 * (finishedCount G c r s L : ℝ)) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ R r d ∧
      (R r d : ℝ) * n / 8 ≤ ∑ v : Fin n, coveredLength G c r s L g v :=
  CGAux.lemma_3_12_core c hr L hL0 hLr s hs hhalf
