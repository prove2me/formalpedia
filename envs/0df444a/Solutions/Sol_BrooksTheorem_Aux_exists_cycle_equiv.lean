-- Prove2me | solution 1 for BrooksTheorem.Aux.exists_cycle_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:36:13.340016+00:00
-- url     : https://prove2.me/submissions/82ae14c3-aac7-4827-9c9f-e7e14cac46dc

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
public import Theorems.Thm_BrooksTheorem_Aux_sq_adj
public import Theorems.Thm_BrooksTheorem_Aux_sq_ne
public import Theorems.Thm_BrooksTheorem_Aux_nb_sq
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (hconn : G.Connected)
    (h2 : ∀ v, (nb G v).card = 2) :
    ∃ n, ∃ e : Fin (n + 3) ≃ V, ∀ i j, (cycleGraph (n + 3)).Adj i j → G.Adj (e i) (e j) := by
  classical
  obtain ⟨v0⟩ := hconn.nonempty
  obtain ⟨v1, hv1⟩ : (nb G v0).Nonempty := by rw [← card_pos, h2]; omega
  rw [mem_nb] at hv1
  have hadj := sq_adj G h2 v0 v1 hv1
  have hne := sq_ne G h2 v0 v1
  have hnb := nb_sq G h2 v0 v1 hv1
  set s := sq G v0 v1 with hs
  have hex : ∃ m, ∃ j < m, s j = s m := by
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card V + 1) => s i.val) (by simp)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact ⟨b.val, a.val, h, he⟩
    · exact ⟨a.val, b.val, h, he.symm⟩
  set m := Nat.find hex with hmdef
  obtain ⟨j, hjm, hsj⟩ := Nat.find_spec hex
  have hmin : ∀ a b, a < b → b < m → s a ≠ s b := by
    intro a b hab hbm he
    exact Nat.find_min hex hbm ⟨a, hab, he⟩
  rw [← hmdef] at hjm hsj
  have hj0 : j = 0 := by
    by_contra hj0
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm'] at hsj hjm
    have h1 : s m' ∈ nb G (s (j' + 1)) := by
      rw [hsj]; exact mem_nb.2 (hadj m').symm
    rw [hnb, mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact hmin j' m' (by omega) (by omega) h1.symm
    · rcases lt_trichotomy (j' + 2) m' with h | h | h
      · exact hmin (j' + 2) m' h (by omega) h1.symm
      · subst h
        have := hne (j' + 1)
        rw [show j' + 1 + 2 = j' + 2 + 1 by omega] at this
        exact this hsj.symm
      · have : j' + 1 = m' := by omega
        subst this
        exact G.loopless.irrefl _ (h1 ▸ hadj (j' + 1))
  subst hj0
  have hm3 : 3 ≤ m := by
    by_contra h
    interval_cases m
    · have := hadj 0
      rw [zero_add, ← hsj] at this
      exact G.loopless.irrefl _ this
    · exact hne 0 hsj.symm
  have hm1 : s (m + 1) = s 1 := by
    have h1 : s 1 ∈ nb G (s (m - 1 + 1)) := by
      rw [show m - 1 + 1 = m by omega, ← hsj]; exact mem_nb.2 (hadj 0)
    rw [hnb, mem_insert, mem_singleton, show m - 1 + 2 = m + 1 by omega] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (hmin 1 (m - 1) (by omega) (by omega))
    · exact h1.symm
  have hper : ∀ t, pseq G v0 v1 (t + m) = pseq G v0 v1 t := by
    intro t
    induction t with
    | zero =>
      rw [zero_add]
      exact Prod.ext hsj.symm hm1
    | succ t iht =>
      rw [show t + 1 + m = (t + m) + 1 by omega]
      simp only [pseq, iht]
  have hper' : ∀ t, s (t + m) = s t := fun t => by
    simp only [hs, sq, hper]
  have hmod : ∀ t, s t = s (t % m) := by
    intro t
    have key : ∀ q r, s (r + m * q) = s r := by
      intro q
      induction q with
      | zero => simp
      | succ q ihq => intro r; rw [mul_add, mul_one, ← add_assoc, hper', ihq]
    conv_lhs => rw [← Nat.mod_add_div t m]
    exact key _ _
  clear_value m
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  let e : Fin (n + 3) → V := fun i => s i.val
  have hinj : Function.Injective e := by
    intro a b hab
    by_contra hne'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · exact hmin a b h b.isLt hab
    · exact hmin b a h a.isLt hab.symm
  have hrange : ∀ {a b : V} (p : G.Walk a b), (∃ i, s i = a) → ∃ i, s i = b := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons u c w hac p ihp =>
      rintro ⟨i, rfl⟩
      apply ihp
      have h1 : c ∈ nb G (s (i + (n + 3) - 1 + 1)) := by
        rw [show i + (n + 3) - 1 + 1 = i + (n + 3) by omega, hper']; exact mem_nb.2 hac
      rw [hnb, mem_insert, mem_singleton] at h1
      rcases h1 with h1 | h1
      · exact ⟨_, h1.symm⟩
      · exact ⟨_, h1.symm⟩
  have hsurj : Function.Surjective e := by
    intro v
    obtain ⟨i, hi⟩ := hrange (hconn.preconnected v0 v).some ⟨0, rfl⟩
    exact ⟨⟨i % (n + 3), Nat.mod_lt _ (by omega)⟩, by simp only [e]; rw [← hmod, hi]⟩
  have hstep : ∀ i : Fin (n + 3), G.Adj (e i) (e (i + 1)) := by
    intro i
    change G.Adj (s i.val) (s (i + 1).val)
    rw [Fin.val_add, Fin.val_one, ← hmod]
    exact hadj _
  refine ⟨n, Equiv.ofBijective e ⟨hinj, hsurj⟩, ?_⟩
  intro i j hij
  change G.Adj (e i) (e j)
  rw [cycleGraph_adj] at hij
  rcases hij with h | h
  · rw [sub_eq_iff_eq_add'] at h
    rw [h]
    exact (hstep j).symm
  · rw [sub_eq_iff_eq_add'] at h
    rw [h]
    exact hstep i
end BrooksTheorem.Aux
