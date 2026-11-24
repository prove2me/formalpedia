-- Prove2me | solution 1 for EquivarianceConvolution.fourier_quotient_sparsity
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:30:47.672743+00:00
-- url     : https://prove2.me/submissions/b42419fe-afbe-4610-84a4-d36b04e81b37

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

universe u

namespace EquivarianceConvolution

open scoped BigOperators

theorem ec3_mul_right {G : Type u} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (f : G → ℂ) (h : G) (hf : ∀ u, f (u * h) = f u) :
    groupFourier ρ f * ρ h = groupFourier ρ f := by
  unfold groupFourier
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, ← map_mul]
  calc ∑ u, f u • ρ (u * h) = ∑ u, f (u * h) • ρ (u * h) := by simp_rw [hf]
    _ = ∑ u, f u • ρ u := Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun _ => rfl)

theorem ec3_mul_left {G : Type u} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (f : G → ℂ) (h : G) (hf : ∀ u, f (h * u) = f u) :
    ρ h * groupFourier ρ f = groupFourier ρ f := by
  unfold groupFourier
  rw [Finset.mul_sum]
  simp_rw [mul_smul_comm, ← map_mul]
  calc ∑ u, f u • ρ (h * u) = ∑ u, f (h * u) • ρ (h * u) := by simp_rw [hf]
    _ = ∑ u, f u • ρ u := Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)

theorem ec3_A {G : Type u} [Group G] {n k : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (H : Subgroup G) (b : Fin n → Fin k) (hb : IsRestrictionDecomp H ρ b)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ h ∈ H, M * ρ h = M) (i j : Fin n)
    (hj : ¬ IsTrivialBlock H ρ b (b j)) : M i j = 0 := by
  classical
  obtain ⟨-, hz, hirr⟩ := hb
  set t := b j with ht
  let ι := {l // b l = t}
  let r : ι → ℂ := fun l => M i l.1
  let j0 : ι := ⟨j, rfl⟩
  have heq : ∀ h ∈ H, ∀ j' : ι, ∑ l : ι, r l * ρ h l.1 j'.1 = r j' := by
    intro h hh j'
    have h1 := congrFun (congrFun (hM h hh) i) j'.1
    rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l => b l = t)] at h1
    have h2 : ∑ l : {x // ¬ b x = t}, M i l.1 * ρ h l.1 j'.1 = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      rw [hz h hh l.1 j'.1 (by rw [j'.2]; exact l.2), mul_zero]
    rw [h2, add_zero] at h1
    exact h1
  by_contra hne
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | ∑ l, r l * w l = 0}
      add_mem' := by
        intro a c ha hc
        change ∑ l, r l * a l = 0 at ha
        change ∑ l, r l * c l = 0 at hc
        change ∑ l, r l * (a l + c l) = 0
        simp only [mul_add, Finset.sum_add_distrib]
        rw [ha, hc, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        change ∑ l, r l * x l = 0 at hx
        change ∑ l, r l * (a * x l) = 0
        rw [show ∑ l, r l * (a * x l) = a * ∑ l, r l * x l by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)]
        rw [hx, mul_zero] }
  have hinv : ∀ g ∈ (H : Set G), ∀ w ∈ W,
      Matrix.mulVec ((ρ g).submatrix (fun i : ι => i.1) (fun i => i.1)) w ∈ W := by
    intro g hg w hw
    show ∑ l, r l * Matrix.mulVec _ w l = 0
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have := heq g hg
    calc ∑ y, ∑ x, r x * (ρ g x.1 y.1 * w y) = ∑ y, r y * w y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [← this y, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := hw
  rcases (hirr t).2 W hinv with hW | hW
  · have hall : ∀ l : ι, l = j0 := by
      intro l
      by_contra hl
      have hmem : (r l • (Pi.single j0 (1:ℂ) : ι → ℂ) - r j0 • (Pi.single l 1 : ι → ℂ)) ∈ W := by
        show ∑ m, r m * (r l • (Pi.single j0 (1:ℂ) : ι → ℂ) - r j0 • (Pi.single l 1 : ι → ℂ)) m = 0
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single j0 (fun m _ hm => by simp [hm]) (by simp),
          Finset.sum_eq_single l (fun m _ hm => by simp [hm]) (by simp)]
        simp only [Pi.single_eq_same]
        ring
      rw [hW] at hmem
      have := congrFun ((Submodule.mem_bot ℂ).1 hmem) l
      simp [hl] at this
      exact hne this
    apply hj
    refine ⟨Fintype.card_eq_one_iff.2 ⟨j0, hall⟩, ?_⟩
    intro h hh i' hi'
    have hi'j : i' = j := congrArg Subtype.val (hall ⟨i', hi'⟩)
    rw [hi'j]
    have h1 := heq h hh j0
    rw [Fintype.sum_eq_single j0 (fun l hl => absurd (hall l) hl)] at h1
    exact (mul_eq_left₀ hne).1 h1
  · have hmem : (Pi.single j0 (1:ℂ) : ι → ℂ) ∈ W := hW ▸ Submodule.mem_top
    apply hne
    have : ∑ m, r m * (Pi.single j0 (1:ℂ) : ι → ℂ) m = 0 := hmem
    rw [Finset.sum_eq_single j0 (fun m _ hm => by simp [hm]) (by simp),
      Pi.single_eq_same, mul_one] at this
    exact this

theorem ec3_B {G : Type u} [Group G] {n k : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (H : Subgroup G) (b : Fin n → Fin k) (hb : IsRestrictionDecomp H ρ b)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ h ∈ H, ρ h * M = M) (i j : Fin n)
    (hi : ¬ IsTrivialBlock H ρ b (b i)) : M i j = 0 := by
  classical
  obtain ⟨-, hz, hirr⟩ := hb
  set t := b i with ht
  let ι := {l // b l = t}
  let c : ι → ℂ := fun l => M l.1 j
  let i0 : ι := ⟨i, rfl⟩
  have heq : ∀ h ∈ H, ∀ l' : ι, ∑ m : ι, ρ h l'.1 m.1 * c m = c l' := by
    intro h hh l'
    have h1 := congrFun (congrFun (hM h hh) l'.1) j
    rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l => b l = t)] at h1
    have h2 : ∑ m : {x // ¬ b x = t}, ρ h l'.1 m.1 * M m.1 j = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      rw [hz h hh l'.1 m.1 (by rw [l'.2]; exact fun e => m.2 e.symm), zero_mul]
    rw [h2, add_zero] at h1
    exact h1
  by_contra hne
  let W : Submodule ℂ (ι → ℂ) := Submodule.span ℂ {c}
  have hinv : ∀ g ∈ (H : Set G), ∀ w ∈ W,
      Matrix.mulVec ((ρ g).submatrix (fun i : ι => i.1) (fun i => i.1)) w ∈ W := by
    intro g hg w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [Matrix.mulVec_smul]
    have : Matrix.mulVec ((ρ g).submatrix (fun i : ι => i.1) (fun i => i.1)) c = c :=
      funext (heq g hg)
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)
  rcases (hirr t).2 W hinv with hW | hW
  · have : c ∈ W := Submodule.mem_span_singleton_self c
    rw [hW, Submodule.mem_bot] at this
    exact hne (congrFun this i0)
  · have hall : ∀ l : ι, l = i0 := by
      intro l
      by_contra hl
      have hmem : (Pi.single l (1:ℂ) : ι → ℂ) ∈ W := hW ▸ Submodule.mem_top
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
      have e1 : a * c i0 = 0 := by
        have := congrFun ha i0
        simpa [Pi.single_apply, Ne.symm hl] using this
      have e2 : a * c l = 1 := by
        have := congrFun ha l
        simpa [Pi.single_apply] using this
      rcases mul_eq_zero.1 e1 with h0 | h0
      · rw [h0, zero_mul] at e2; exact zero_ne_one e2
      · exact hne h0
    apply hi
    refine ⟨Fintype.card_eq_one_iff.2 ⟨i0, hall⟩, ?_⟩
    intro h hh i' hi'
    have hi'i : i' = i := congrArg Subtype.val (hall ⟨i', hi'⟩)
    rw [hi'i]
    have h1 := heq h hh i0
    rw [Fintype.sum_eq_single i0 (fun l hl => absurd (hall l) hl)] at h1
    exact (mul_eq_right₀ hne).1 h1

end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G : Type u} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (_hρ : IsIrrep ρ) (H : Subgroup G) {k : ℕ}
    (bH : Fin n → Fin k) (hbH : IsRestrictionDecomp H ρ bH) :
    (∀ (f : G ⧸ H → ℂ) (i j : Fin n), ¬ IsTrivialBlock H ρ bH (bH j) →
      groupFourier ρ (liftQ f) i j = 0) ∧
    (∀ (f : Quotient (QuotientGroup.rightRel H) → ℂ) (i j : Fin n),
      ¬ IsTrivialBlock H ρ bH (bH i) → groupFourier ρ (liftR f) i j = 0) ∧
    (∀ (K : Subgroup G) (k' : ℕ) (bK : Fin n → Fin k'), IsRestrictionDecomp K ρ bK →
      ∀ (f : G → ℂ), IsDoubleCosetFun H K f → ∀ i j : Fin n,
        (¬ IsTrivialBlock H ρ bH (bH i) ∨ ¬ IsTrivialBlock K ρ bK (bK j)) →
          groupFourier ρ f i j = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f i j hj
    exact ec3_A ρ H bH hbH _ (fun h hh => ec3_mul_right ρ _ h
      (fun u => by simp only [liftQ, QuotientGroup.mk_mul_of_mem u hh])) i j hj
  · intro f i j hi
    exact ec3_B ρ H bH hbH _ (fun h hh => ec3_mul_left ρ _ h (fun u => by
      unfold liftR
      congr 1
      exact Quotient.sound (QuotientGroup.rightRel_apply.2 (by simpa using hh)))) i j hi
  · intro K k' bK hbK f hf i j hij
    rcases hij with hi | hj
    · exact ec3_B ρ H bH hbH _ (fun h hh => ec3_mul_left ρ f h
        (fun u => by simpa using hf h hh 1 K.one_mem u)) i j hi
    · exact ec3_A ρ K bK hbK _ (fun k hk => ec3_mul_right ρ f k
        (fun u => by simpa using hf 1 H.one_mem k hk u)) i j hj
