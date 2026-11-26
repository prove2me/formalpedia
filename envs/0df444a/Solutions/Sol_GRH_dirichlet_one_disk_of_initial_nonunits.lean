-- Prove2me | solution 1 for GRH.dirichlet_one_disk_of_initial_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:36:37.757276+00:00
-- url     : https://prove2.me/submissions/3e5d3580-608e-4f2f-b58f-f43a89154bf4

import Theorems.Thm_GRH_dirichlet_one_disk_of_period_variation
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma half_prefix (v : ℕ → ℕ) (hv : ∀ k, v k ≤ 1) :
    ∀ n b : ℕ, b ≤ ∑ k ∈ Finset.range n, v k →
      ∃ t ≤ n, (∑ k ∈ Finset.range t, v k) = b := by
  intro n
  induction n with
  | zero =>
    intro b hb
    simp only [Finset.sum_range_zero, Nat.le_zero] at hb
    exact ⟨0,le_rfl,by simp [hb]⟩
  | succ n ih =>
    intro b hb
    by_cases h : b ≤ ∑ k ∈ Finset.range n, v k
    · obtain ⟨t,ht,he⟩ := ih b h
      exact ⟨t,by omega,he⟩
    · refine ⟨n+1,le_rfl,?_⟩
      rw [Finset.sum_range_succ] at hb ⊢
      have := hv n
      omega

/-- An initial gap among the reduced residues yields a totient-sensitive
disk about 1 for every nonprincipal character of that level. -/
theorem solution (q : ℕ) [NeZero q] (hq : 2 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℕ) (hM : 0 < M) (hgap : ∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime q)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s - 1‖ ≤ ((q.totient:ℝ)/4)*(1+‖s‖/s.re)*((M:ℝ)+1)^(-s.re) := by
  let v (k : ℕ) : ℕ := if q.Coprime (k+1) then 1 else 0
  have cap : ∀ k, v k ≤ 1 := fun k => by dsimp [v]; split <;> omega
  have total : ∑ k ∈ Finset.range q, v k = q.totient := by
    have h : (∑ k ∈ Finset.Ico 1 (1+q), if q.Coprime k then (1:ℕ) else 0) = q.totient := by
      simpa only [Finset.sum_boole, Nat.cast_id] using Nat.filter_coprime_Ico_eq_totient q 1
    rw [Finset.sum_Ico_eq_sum_range] at h
    simpa [v,Nat.add_comm] using h
  have norm (k : ℕ) : ‖χ ((k+1:ℕ):ZMod q)‖ ≤ (v k:ℝ) := by
    by_cases h : q.Coprime (k+1)
    · rw [show v k=1 from if_pos h,Nat.cast_one]
      exact χ.norm_le_one _
    · have nunit : ¬ IsUnit ((k+1:ℕ):ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun h' => h h'.symm
      rw [show v k=0 from if_neg h,Nat.cast_zero,MulChar.map_nonunit χ nunit,norm_zero]
  obtain ⟨b,hb⟩ := Nat.totient_even hq
  obtain ⟨t,ht,he⟩ := half_prefix v cap q b (by omega)
  have back := Finset.sum_range_add_sum_Ico v ht
  rw [he,total,hb] at back
  have back' : (∑ k ∈ Finset.Ico t q, v k) = b := by omega
  have count (S : Finset ℕ) (hS : (∑ k ∈ S,v k)=b) :
      (∑ k ∈ S, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ (b:ℝ) := by
    apply (Finset.sum_le_sum (fun k (_ : k ∈ S) => norm k)).trans_eq
    exact_mod_cast hS
  have bnd := GRH.dirichlet_one_disk_of_period_variation q χ hχ t M b ht hM
    (count _ he) (count _ back') (fun k hk hkM =>
      MulChar.map_nonunit χ (fun hu => hgap (k+1) (by omega) (by omega)
        ((ZMod.isUnit_iff_coprime (k+1) q).1 hu))) s hs
  have scal : (b:ℝ)/2=(q.totient:ℝ)/4 := by rw [hb]; push_cast; ring
  rwa [scal] at bnd
