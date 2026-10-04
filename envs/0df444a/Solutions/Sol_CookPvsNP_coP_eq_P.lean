-- Prove2me | solution 1 for CookPvsNP.coP_eq_P
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:32:22.646985+00:00
-- url     : https://prove2.me/submissions/11472e11-013a-48db-b25b-957fe78fceda

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CookPvsNPCoP

open CookPvsNP

/-- The machine with accepting and rejecting states swapped. -/
abbrev swapTM {Γ : Type} (M : TM Γ) : TM Γ :=
  { Q := M.Q, finQ := M.finQ, decQ := M.decQ, q₀ := M.q₀, qaccept := M.qreject,
    qreject := M.qaccept, accept_ne_reject := M.accept_ne_reject.symm, δ := M.δ }

theorem swap_isHalting {Γ : Type} (M : TM Γ) (c : Cfg Γ M.Q) :
    (swapTM M).IsHalting c ↔ M.IsHalting c := by
  simp only [TM.IsHalting, swapTM]
  exact or_comm

theorem swap_step {Γ : Type} (M : TM Γ) (c : Cfg Γ M.Q) :
    (swapTM M).step c = M.step c := by
  unfold TM.step
  have hi := swap_isHalting M c
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hi.1 h1) h2
  · exact absurd (hi.2 h2) h1
  · have hd : (swapTM M).δ c.state c.head = M.δ c.state c.head := rfl
    rw [hd]
    obtain ⟨st, l, hh, r⟩ := c
    rcases h : M.δ st hh with ⟨q', s', mv⟩
    rcases mv with _ | _ <;> rcases l with _ | ⟨a, l⟩ <;> rfl

theorem swap_run {Γ : Type} (M : TM Γ) (n : ℕ) (c : Cfg Γ M.Q) :
    (swapTM M).run n c = M.run n c := by
  unfold TM.run
  have : (swapTM M).step = M.step := funext (swap_step M)
  rw [this]

theorem swap_init {Γ : Type} (M : TM Γ) (w : List Γ) :
    (swapTM M).init w = M.init w := rfl

theorem run_stable {Γ : Type} (M : TM Γ) (c : Cfg Γ M.Q) (n : ℕ)
    (h : M.IsHalting (M.run n c)) : ∀ m, n ≤ m → M.run m c = M.run n c := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    have e : M.run (n + (d + 1)) c = M.step (M.run (n + d) c) := by
      unfold TM.run
      rw [show n + (d + 1) = (n + d) + 1 from rfl, Function.iterate_succ_apply']
    rw [e, ih (by omega)]
    unfold TM.step
    rw [if_pos h]

theorem accepts_iff {Γ : Type} (M : TM Γ) (w : List Γ) (N : ℕ) (hN : M.HaltsWithin N w) :
    M.Accepts w ↔ (M.run N (M.init w)).state = M.qaccept := by
  constructor
  · rintro ⟨n, hn⟩
    have hh : M.IsHalting (M.run n (M.init w)) := Or.inl hn
    have h1 := run_stable M (M.init w) n hh (max n N) (le_max_left _ _)
    have h2 := run_stable M (M.init w) N hN (max n N) (le_max_right _ _)
    rw [← h2, h1]; exact hn
  · intro h; exact ⟨N, h⟩

theorem compl_mem_P (Sym : Type) [Fintype Sym] (L : Lang Sym) (hL : L ∈ P Sym) :
    Lᶜ ∈ P Sym := by
  obtain ⟨Γ, hΓ, ι, M, k, hhalt, hacc⟩ := hL
  refine ⟨Γ, hΓ, ι, swapTM M, k, ?_, ?_⟩
  · intro w
    have := hhalt w
    unfold TM.HaltsWithin at this ⊢
    rw [swap_init, swap_run, swap_isHalting]
    exact this
  · intro w
    have hN : (swapTM M).HaltsWithin (w.length ^ k + k) (w.map ι) := by
      have := hhalt w
      unfold TM.HaltsWithin at this ⊢
      rw [swap_init, swap_run, swap_isHalting]
      exact this
    rw [accepts_iff (swapTM M) _ _ hN, swap_init, swap_run, Set.mem_compl_iff, hacc w,
      accepts_iff M _ _ (hhalt w)]
    have hH := hhalt w
    unfold TM.HaltsWithin TM.IsHalting at hH
    show ¬ _ ↔ _ = M.qreject
    rcases hH with h | h
    · rw [h]; exact ⟨fun hn => absurd rfl hn, fun he => absurd he M.accept_ne_reject⟩
    · rw [h]; exact ⟨fun _ => rfl, fun _ he => M.accept_ne_reject he.symm⟩

end CookPvsNPCoP

open CookPvsNP in
theorem solution (Sym : Type) [Fintype Sym] : { L : Lang Sym | Lᶜ ∈ P Sym } = P Sym := by
  ext L
  constructor
  · intro h
    have := CookPvsNPCoP.compl_mem_P Sym Lᶜ h
    simpa using this
  · intro h
    exact CookPvsNPCoP.compl_mem_P Sym L h
