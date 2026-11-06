-- Prove2me | solution 1 for FlowJobHardness.ColoringReduction.remark_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:17:59.265763+00:00
-- url     : https://prove2.me/submissions/6140dfc9-cf25-4f36-b5b9-001bac63444b

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

end CGAux

open FlowJobHardness.ColoringReduction in
theorem solution {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : G.Coloring (Fin d)) (r : ℕ) :
    (∀ q : Fin (size r d n), (inst G c r).jobLength q = (R r d : ℝ)) ∧
    (∀ p : Fin (size r d n), (inst G c r).load p = (R r d : ℝ)) ∧
    (∀ Δ : ℕ, (∀ v : Fin n, G.degree v ≤ Δ) →
      ∀ q : Fin (size r d n), (inst G c r).μ q ≤ (Δ + 1) * R r d) :=
  ⟨CGAux.jobLength_eq c, CGAux.load_eq c, fun Δ hΔ q => CGAux.mu_le c q Δ hΔ⟩
