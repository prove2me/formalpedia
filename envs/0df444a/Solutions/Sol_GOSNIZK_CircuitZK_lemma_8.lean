-- Prove2me | solution 1 for GOSNIZK.CircuitZK.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T11:18:38.966363+00:00
-- url     : https://prove2.me/submissions/7681b1f2-3870-4512-9f26-e5350be90635

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_ZKGame

set_option autoImplicit false

namespace GOSNIZK.CircuitZK.L8Aux

/-- Value of a pushforward of a uniform law, as a count. -/
theorem map_unif_apply {α β : Type} [Fintype α] [Nonempty α] [DecidableEq β] (F : α → β) (y : β) :
    (PMF.uniformOfFintype α).map F y =
      ((Finset.univ.filter (fun a => y = F a)).card : ENNReal) * (Fintype.card α : ENNReal)⁻¹ := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem map_unif_eq_iff {α β : Type} [Fintype α] [Nonempty α] [DecidableEq β] (F G : α → β) :
    (PMF.uniformOfFintype α).map F = (PMF.uniformOfFintype α).map G ↔
      ∀ y, (Finset.univ.filter (fun a => y = F a)).card =
        (Finset.univ.filter (fun a => y = G a)).card := by
  constructor
  · intro h y
    have hy := congrArg (fun p : PMF β => p y) h
    simp only [map_unif_apply] at hy
    have hc : (Fintype.card α : ENNReal)⁻¹ ≠ 0 := by
      simp
    have := (ENNReal.mul_left_inj hc (by simp)).1 hy
    exact_mod_cast this
  · intro h
    ext y
    rw [map_unif_apply, map_unif_apply, h y]

/-- Product of independent coordinates with equal marginals. -/
theorem map_pair_eq {A B β γ : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq β] [DecidableEq γ]
    (F1 G1 : A → β) (F2 G2 : B → γ)
    (h1 : (PMF.uniformOfFintype A).map F1 = (PMF.uniformOfFintype A).map G1)
    (h2 : (PMF.uniformOfFintype B).map F2 = (PMF.uniformOfFintype B).map G2) :
    (PMF.uniformOfFintype (A × B)).map (fun p => (F1 p.1, F2 p.2)) =
      (PMF.uniformOfFintype (A × B)).map (fun p => (G1 p.1, G2 p.2)) := by
  rw [map_unif_eq_iff] at h1 h2 ⊢
  intro y
  have e : ∀ (H1 : A → β) (H2 : B → γ),
      Finset.univ.filter (fun p : A × B => y = (H1 p.1, H2 p.2)) =
        (Finset.univ.filter (fun a => y.1 = H1 a)) ×ˢ (Finset.univ.filter (fun b => y.2 = H2 b)) := by
    intro H1 H2
    ext p
    simp [Prod.ext_iff]
  rw [e, e, Finset.card_product, Finset.card_product, h1 y.1, h2 y.2]

/-- Coordinatewise maps with equal marginals. -/
theorem map_pi_eq {ι X β : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    [DecidableEq β]
    (f g : ι → X → β)
    (h : ∀ i, (PMF.uniformOfFintype X).map (f i) = (PMF.uniformOfFintype X).map (g i)) :
    (PMF.uniformOfFintype (ι → X)).map (fun ρ i => f i (ρ i)) =
      (PMF.uniformOfFintype (ι → X)).map (fun ρ i => g i (ρ i)) := by
  rw [map_unif_eq_iff]
  intro y
  have e : ∀ k : ι → X → β,
      Finset.univ.filter (fun ρ : ι → X => y = fun i => k i (ρ i)) =
        Fintype.piFinset (fun i => Finset.univ.filter (fun x => y i = k i x)) := by
    intro k
    ext ρ
    simp [Fintype.mem_piFinset, funext_iff]
  rw [e, e, Fintype.card_piFinset, Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (map_unif_eq_iff _ _).1 (h i) (y i)

/-- Change of variables in the first coordinate. -/
theorem map_prod_shift {A B β : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq β]
    (F G : A → B → β) (φ : A ≃ A)
    (h : ∀ a, (PMF.uniformOfFintype B).map (F a) = (PMF.uniformOfFintype B).map (G (φ a))) :
    (PMF.uniformOfFintype (A × B)).map (fun p => F p.1 p.2) =
      (PMF.uniformOfFintype (A × B)).map (fun p => G p.1 p.2) := by
  rw [map_unif_eq_iff]
  intro y
  have e : ∀ K : A → B → β,
      (Finset.univ.filter (fun p : A × B => y = K p.1 p.2)).card =
        ∑ a, (Finset.univ.filter (fun b => y = K a b)).card := by
    intro K
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.card_filter]
  rw [e, e]
  rw [← Equiv.sum_comp φ (fun a => (Finset.univ.filter (fun b => y = G a b)).card)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact (map_unif_eq_iff _ _).1 (h a) y

end GOSNIZK.CircuitZK.L8Aux

namespace GOSNIZK.CircuitZK

open L8Aux

variable {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]

theorem l8_shift (S : Scheme N R C CK XK TK Rp Pf) (hhom : S.Homomorphic)
    (hTO : S.PerfectTrapdoorOpening) (kt : CK × TK) (hkt : kt ∈ S.Khide.support) (r : R) :
    S.com kt.1 1 r = S.com kt.1 0 (r + S.Topen kt.2 1 0 0) := by
  have hck : (∃ xk, (kt.1, xk) ∈ S.Kbind.support) ∨ (∃ tk, (kt.1, tk) ∈ S.Khide.support) :=
    Or.inr ⟨kt.2, hkt⟩
  have h1 := hhom kt.1 hck 1 0 0 r
  have h2 := hTO kt hkt 1 0 0
  have h3 := hhom kt.1 hck 0 0 (S.Topen kt.2 1 0 0) r
  simp only [add_zero, zero_add] at h1 h3
  rw [h1, ← h2, ← h3, add_comm]

/-- On a hiding key, the law of a 0/1 proof depends only on the commitment. -/
theorem l8_P01_law [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Pf)
    (hhom : S.Homomorphic) (hTO : S.PerfectTrapdoorOpening) (hWI : S.PerfectWI)
    (kt : CK × TK) (hkt : kt ∈ S.Khide.support) (m₁ m₂ : ZMod N) (r₁ r₂ : R)
    (hm₁ : m₁ = 0 ∨ m₁ = 1) (hm₂ : m₂ = 0 ∨ m₂ = 1)
    (hc : S.com kt.1 m₁ r₁ = S.com kt.1 m₂ r₂) :
    (PMF.uniformOfFintype Rp).map (S.P01 kt.1 m₁ r₁) =
      (PMF.uniformOfFintype Rp).map (S.P01 kt.1 m₂ r₂) := by
  set t := S.Topen kt.2 1 0 0
  -- every opening has the law of a 0-opening of the same commitment
  have to0 : ∀ (m : ZMod N) (r : R), (m = 0 ∨ m = 1) → ∃ s, S.com kt.1 0 s = S.com kt.1 m r ∧
      (PMF.uniformOfFintype Rp).map (S.P01 kt.1 m r) =
        (PMF.uniformOfFintype Rp).map (S.P01 kt.1 0 s) := by
    intro m r hm
    rcases hm with hm | hm
    · subst hm; exact ⟨r, rfl, rfl⟩
    · subst hm
      have hs := l8_shift S hhom hTO kt hkt r
      exact ⟨r + t, hs.symm, (hWI kt hkt (r + t) r hs.symm).symm⟩
  -- two 0-openings of the same commitment have the same law
  have zz : ∀ s₁ s₂ : R, S.com kt.1 0 s₁ = S.com kt.1 0 s₂ →
      (PMF.uniformOfFintype Rp).map (S.P01 kt.1 0 s₁) =
        (PMF.uniformOfFintype Rp).map (S.P01 kt.1 0 s₂) := by
    intro s₁ s₂ h
    have hu : S.com kt.1 1 (s₁ - t) = S.com kt.1 0 s₁ := by
      rw [l8_shift S hhom hTO kt hkt, sub_add_cancel]
    rw [hWI kt hkt s₁ (s₁ - t) hu.symm, hWI kt hkt s₂ (s₁ - t) (h.symm.trans hu.symm)]
  obtain ⟨s₁, hs₁, e₁⟩ := to0 m₁ r₁ hm₁
  obtain ⟨s₂, hs₂, e₂⟩ := to0 m₂ r₂ hm₂
  rw [e₁, e₂]
  exact zz s₁ s₂ (by rw [hs₁, hs₂, hc])

theorem l8_prove_eq [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp]
    (S : Scheme N R C CK XK TK Rp Pf) (hhom : S.Homomorphic) (hTO : S.PerfectTrapdoorOpening)
    (hWI : S.PerfectWI) (kt : CK × TK) (hkt : kt ∈ S.Khide.support) {n : ℕ} (Γ : Circuit n)
    (w : Fin n → Bool) (hsat : Γ.Sat w) :
    prove S kt.1 Γ w = simulate S kt.1 kt.2 Γ := by
  classical
  have hck : (∃ xk, (kt.1, xk) ∈ S.Kbind.support) ∨ (∃ tk, (kt.1, tk) ∈ S.Khide.support) :=
    Or.inr ⟨kt.2, hkt⟩
  set t := S.Topen kt.2 1 0 0 with ht
  let δ : Fin n → R := fun i => if i ≠ Γ.out ∧ w i = true then t else 0
  let m : Fin n → ZMod N := fun i => if i = Γ.out then 1 else 0
  have hout : w Γ.out = true := hsat.2
  have CW : ∀ (r : Fin n → R) (i : Fin n),
      S.com kt.1 (bit (w i)) (wireRand Γ r i) = S.com kt.1 (m i) (wireRand Γ (r + δ) i) := by
    intro r i
    by_cases hi : i = Γ.out
    · subst hi; simp [wireRand, m, bit, hout]
    · cases hw : w i
      · simp [wireRand, m, bit, hi, hw, δ]
      · simp [wireRand, m, bit, hi, hw, δ]
        exact l8_shift S hhom hTO kt hkt (r i)
  have bit01 : ∀ b : Bool, (bit b : ZMod N) = 0 ∨ (bit b : ZMod N) = 1 := by
    intro b; cases b <;> simp [bit]
  have m01 : ∀ i, m i = 0 ∨ m i = 1 := by
    intro i; by_cases hi : i = Γ.out <;> simp [m, hi]
  have expand : ∀ (a b c : ZMod N) (x y z : R),
      S.com kt.1 (a + b + 2 * c - 2) (x + y + 2 • z) =
        S.com kt.1 a x * S.com kt.1 b y * S.com kt.1 c z * S.com kt.1 c z * S.com kt.1 (-2) 0 := by
    intro a b c x y z
    have H := hhom kt.1 hck
    have e1 : a + b + 2 * c - 2 = a + b + c + c + (-2) := by ring
    have e2 : x + y + 2 • z = x + y + z + z + 0 := by abel
    rw [e1, e2, H, H, H, H]
  have gate01 : ∀ g ∈ Γ.gates,
      (bit (w g.1) + bit (w g.2.1) + 2 * bit (w g.2.2) - 2 : ZMod N) = 0 ∨
        (bit (w g.1) + bit (w g.2.1) + 2 * bit (w g.2.2) - 2 : ZMod N) = 1 := by
    intro g hg
    rw [hsat.1 g hg]
    cases w g.1 <;> cases w g.2.1 <;>
      simp only [bit, Bool.not_true, Bool.not_false, Bool.and_self, Bool.and_false,
        Bool.false_and, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_true, ite_false,
        if_true, if_false] <;>
      first | (left; ring1) | (right; ring1)
  unfold prove simulate
  refine map_prod_shift (fun r ρ => proveWith S kt.1 Γ w (r, ρ))
    (fun r ρ => simulateWith S kt.1 kt.2 Γ (r, ρ)) (Equiv.addRight δ) ?_
  intro r
  simp only [Equiv.coe_addRight]
  let fwR : Fin n → Rp → Pf := fun i => S.P01 kt.1 (bit (w i)) (wireRand Γ r i)
  let fwS : Fin n → Rp → Pf := fun i => S.P01 kt.1 (m i) (wireRand Γ (r + δ) i)
  let fgR : Fin Γ.gates.length → Rp → Pf := fun g =>
    S.P01 kt.1 (bit (w (Γ.gates.get g).1) + bit (w (Γ.gates.get g).2.1)
        + 2 * bit (w (Γ.gates.get g).2.2) - 2)
      (wireRand Γ r (Γ.gates.get g).1 + wireRand Γ r (Γ.gates.get g).2.1
        + 2 • wireRand Γ r (Γ.gates.get g).2.2)
  let fgS : Fin Γ.gates.length → Rp → Pf := fun g =>
    S.P01 kt.1 0 (S.Topen kt.2 (m (Γ.gates.get g).1 + m (Γ.gates.get g).2.1
        + 2 * m (Γ.gates.get g).2.2 - 2)
      (wireRand Γ (r + δ) (Γ.gates.get g).1 + wireRand Γ (r + δ) (Γ.gates.get g).2.1
        + 2 • wireRand Γ (r + δ) (Γ.gates.get g).2.2) 0)
  let H : (Fin n → Pf) × (Fin Γ.gates.length → Pf) → Proof C Pf := fun v =>
    { coms := List.ofFn fun i => S.com kt.1 (m i) (wireRand Γ (r + δ) i)
      wireProofs := List.ofFn v.1
      gateProofs := List.ofFn v.2 }
  have hR : (fun ρ : (Fin n → Rp) × (Fin Γ.gates.length → Rp) => proveWith S kt.1 Γ w (r, ρ)) =
      H ∘ (fun ρ => ((fun i => fwR i (ρ.1 i)), (fun g => fgR g (ρ.2 g)))) := by
    funext ρ
    simp only [proveWith, H, Function.comp_apply, fwR, fgR]
    congr 1
    congr 1
    funext i
    by_cases hi : i = Γ.out
    · subst hi; simp [m, wireRand]
    · rw [if_neg hi]; exact CW r i
  have hS : (fun ρ : (Fin n → Rp) × (Fin Γ.gates.length → Rp) =>
      simulateWith S kt.1 kt.2 Γ (r + δ, ρ)) =
      H ∘ (fun ρ => ((fun i => fwS i (ρ.1 i)), (fun g => fgS g (ρ.2 g)))) := by
    funext ρ
    simp only [simulateWith, H, Function.comp_apply, fwS, fgS, m]
  rw [hR, hS, ← PMF.map_comp, ← PMF.map_comp]
  congr 1
  refine map_pair_eq _ _ _ _ (map_pi_eq fwR fwS ?_) (map_pi_eq fgR fgS ?_)
  · intro i
    exact l8_P01_law S hhom hTO hWI kt hkt _ _ _ _ (bit01 _) (m01 i) (CW r i)
  · intro g
    refine l8_P01_law S hhom hTO hWI kt hkt _ _ _ _ (gate01 _ (List.get_mem _ _)) (Or.inl rfl) ?_
    rw [hTO kt hkt, expand, expand, CW r (Γ.gates.get g).1, CW r (Γ.gates.get g).2.1,
      CW r (Γ.gates.get g).2.2]

end GOSNIZK.CircuitZK

open GOSNIZK.CircuitZK in
theorem solution {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
    [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp] (hN : 4 ≤ N)
    (S : Scheme N R C CK XK TK Rp Pf) (hhom : S.Homomorphic) (hTO : S.PerfectTrapdoorOpening)
    (hTOI : S.PerfectTrapdoorOpeningIndist) (hWI : S.PerfectWI)
    (A : CK → Adv Query (Option (Proof C Pf))) :
    (S.Khide.bind fun kt => (A kt.1).run (realOracle S kt.1)) =
      (S.Khide.bind fun kt => (A kt.1).run (simOracle S kt.1 kt.2)) := by
  have key : ∀ kt ∈ S.Khide.support, realOracle S kt.1 = simOracle S kt.1 kt.2 := by
    intro kt hkt
    funext q
    unfold realOracle simOracle
    split_ifs with h
    · rw [l8_prove_eq S hhom hTO hWI kt hkt q.2.1 q.2.2 h]
    · rfl
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr (fun kt => ?_)
  by_cases hkt : kt ∈ S.Khide.support
  · rw [key kt hkt]
  · rw [(PMF.apply_eq_zero_iff _ _).2 hkt, zero_mul, zero_mul]
