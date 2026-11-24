-- Prove2me | solution 1 for GaussPolyReg.Approx.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T02:37:45.930316+00:00
-- url     : https://prove2.me/submissions/f148c8a3-0904-42e7-97db-70363687592d

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx
open Finset

namespace FinnerAux

variable {V E α : Type} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E]
  [Fintype α] [DecidableEq α]

def P (φ0 : E → α) (t : Finset E) : Finset (E → α) :=
  univ.filter (fun φ => ∀ e, e ∉ t → φ e = φ0 e)

lemma sum_P_insert (φ0 : E → α) (t : Finset E) (e : E) (he : e ∉ t) (h : (E → α) → ℝ) :
    ∑ φ ∈ P φ0 (insert e t), h φ = ∑ φ' ∈ P φ0 t, ∑ x : α, h (Function.update φ' e x) := by
  rw [← Finset.sum_product' (f := fun φ' x => h (Function.update φ' e x))]
  refine Finset.sum_nbij' (fun φ => (Function.update φ e (φ0 e), φ e))
    (fun p => Function.update p.1 e p.2) ?_ ?_ ?_ ?_ ?_
  · intro φ hφ
    simp only [P, mem_filter, mem_univ, true_and, mem_insert, not_or, mem_product] at hφ ⊢
    refine ⟨fun e' he' => ?_, trivial⟩
    by_cases h' : e' = e
    · subst h'; simp
    · rw [Function.update_of_ne h']; exact hφ e' ⟨h', he'⟩
  · intro p hp
    simp only [P, mem_filter, mem_univ, true_and, mem_insert, not_or, mem_product] at hp ⊢
    intro e' he'
    rw [Function.update_of_ne he'.1]; exact hp.1 e' he'.2
  · intro φ hφ
    simp only [P, mem_filter, mem_univ, true_and, mem_insert, not_or] at hφ
    funext e'
    by_cases h' : e' = e
    · subst h'; simp
    · simp [Function.update_of_ne h']
  · intro p hp
    simp only [P, mem_filter, mem_univ, true_and, mem_insert, not_or, mem_product] at hp
    refine Prod.ext ?_ ?_
    · funext e'
      by_cases h' : e' = e
      · subst h'; simp; exact (hp.1 e' he).symm
      · simp [Function.update_of_ne h']
    · simp
  · intro φ hφ
    congr 1
    funext e'
    by_cases h' : e' = e
    · subst h'; simp
    · simp [Function.update_of_ne h']

lemma P_empty (φ0 : E → α) : P φ0 ∅ = {φ0} := by
  ext φ; simp [P, funext_iff]

theorem finner (φ0 : E → α) (s : Finset E) :
    ∀ (S : V → Finset E) (f : V → (E → α) → ℝ), (∀ c φ, 0 ≤ f c φ) → (∀ c, S c ⊆ s) →
    (∀ c φ ψ, (∀ e ∈ S c, φ e = ψ e) → f c φ = f c ψ) →
    (∀ e ∈ s, ∃ a b, a ≠ b ∧ e ∈ S a ∧ e ∈ S b ∧ ∀ c, e ∈ S c → c = a ∨ c = b) →
    ∑ φ ∈ P φ0 s, ∏ c, f c φ ≤ ∏ c, Real.sqrt (∑ φ ∈ P φ0 (S c), (f c φ) ^ 2) := by
  induction s using Finset.induction_on with
  | empty =>
    intro S f hf hS _ _
    have : ∀ c, S c = ∅ := fun c => Finset.subset_empty.mp (hS c)
    simp only [this, P_empty, sum_singleton]
    refine le_of_eq (Finset.prod_congr rfl fun c _ => ?_)
    rw [Real.sqrt_sq (hf _ _)]
  | insert e s' he ih =>
    intro S f hf hS hdep hstr
    obtain ⟨a, b, hab, haS, hbS, hc⟩ := hstr e (mem_insert_self _ _)
    let g : V → (E → α) → ℝ := fun c φ => Real.sqrt (∑ x : α, (f c (Function.update φ e x)) ^ 2)
    let f' : V → (E → α) → ℝ := fun c φ => if c = a ∨ c = b then g c φ else f c φ
    let S' : V → Finset E := fun c => (S c).erase e
    have hS'c : ∀ c, ¬ (c = a ∨ c = b) → S' c = S c := by
      intro c hc'
      refine Finset.erase_eq_of_notMem fun h => hc' (hc c h)
    have key := ih S' f' ?_ ?_ ?_ ?_
    · rw [sum_P_insert φ0 s' e he]
      refine le_trans ?_ (key.trans (le_of_eq ?_))
      · refine Finset.sum_le_sum fun φ' hφ' => ?_
        have hne : ∀ c, ¬ (c = a ∨ c = b) → ∀ x, f c (Function.update φ' e x) = f c φ' := by
          intro c hc' x
          apply hdep
          intro e' he'
          have : e' ≠ e := fun h => hc' (hc c (h ▸ he'))
          simp [Function.update_of_ne this]
        have split : ∀ h : V → ℝ, ∏ c, h c = h a * (h b * ∏ c ∈ ((univ.erase a).erase b), h c) := by
          intro h
          rw [← Finset.mul_prod_erase univ h (mem_univ a),
            ← Finset.mul_prod_erase (univ.erase a) h (mem_erase.mpr ⟨hab.symm, mem_univ b⟩)]
        have hrest : ∀ x, ∏ c ∈ ((univ.erase a).erase b), f c (Function.update φ' e x)
            = ∏ c ∈ ((univ.erase a).erase b), f' c φ' := by
          intro x
          refine Finset.prod_congr rfl fun c hc2 => ?_
          have h1 : c ≠ b := (mem_erase.mp hc2).1
          have h2 : c ≠ a := (mem_erase.mp (mem_erase.mp hc2).2).1
          have hn : ¬ (c = a ∨ c = b) := by tauto
          simp only [f', if_neg hn]
          exact hne c hn x
        have hrest0 : 0 ≤ ∏ c ∈ ((univ.erase a).erase b), f' c φ' :=
          Finset.prod_nonneg fun c _ => by
            simp only [f']; split_ifs
            · exact Real.sqrt_nonneg _
            · exact hf _ _
        simp_rw [split (fun c => f c (Function.update φ' e _)), hrest]
        rw [split (fun c => f' c φ')]
        simp only [f', true_or, or_true, if_true]
        have cs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset α)
          (fun x => f a (Function.update φ' e x)) (fun x => f b (Function.update φ' e x))
        calc ∑ x, (f a (Function.update φ' e x) * (f b (Function.update φ' e x) *
              ∏ c ∈ ((univ.erase a).erase b), f' c φ'))
            = (∑ x, f a (Function.update φ' e x) * f b (Function.update φ' e x)) *
                ∏ c ∈ ((univ.erase a).erase b), f' c φ' := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => by ring
          _ ≤ _ := by
              refine le_trans (mul_le_mul_of_nonneg_right cs hrest0) (le_of_eq ?_)
              simp only [g]; ring
      · refine Finset.prod_congr rfl fun c _ => ?_
        congr 1
        by_cases hcab : c = a ∨ c = b
        · have heS : e ∈ S c := by rcases hcab with rfl | rfl <;> assumption
          have := sum_P_insert φ0 (S' c) e (by simp [S']) (fun φ => f c φ ^ 2)
          have hins : insert e (S' c) = S c := by simp [S', Finset.insert_erase heS]
          rw [hins] at this
          rw [this]
          refine Finset.sum_congr rfl fun φ' _ => ?_
          simp only [f', if_pos hcab, g]
          rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        · rw [hS'c c hcab]; simp only [f', if_neg hcab]
    · intro c φ; simp only [f']; split_ifs
      · exact Real.sqrt_nonneg _
      · exact hf _ _
    · intro c x hx
      simp only [S', mem_erase] at hx
      have := hS c hx.2
      rcases mem_insert.mp this with h | h
      · exact absurd h hx.1
      · exact h
    · intro c φ ψ hφψ
      simp only [f']
      split_ifs with hcab
      · simp only [g]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hdep c (Function.update φ e x) (Function.update ψ e x)]
        intro e' he'
        by_cases h' : e' = e
        · subst h'; simp
        · simp only [Function.update_of_ne h']
          exact hφψ e' (mem_erase.mpr ⟨h', he'⟩)
      · exact hdep c φ ψ (fun e' he' => hφψ e' (by rw [hS'c c hcab]; exact he'))
    · intro e' he'
      obtain ⟨a', b', h1, h2, h3, h4⟩ := hstr e' (mem_insert_of_mem he')
      have hne : e' ≠ e := fun h => he (h ▸ he')
      refine ⟨a', b', h1, ?_, ?_, ?_⟩
      · exact mem_erase.mpr ⟨hne, h2⟩
      · exact mem_erase.mpr ⟨hne, h3⟩
      · intro c hc2; exact h4 c (mem_erase.mp hc2).2

end FinnerAux


open FinnerAux Classical in
lemma bij_sum {V E : Type} [Fintype V] [Fintype E] (π : Network V E) (hπ : ∀ e, π.src e ≠ π.tgt e)
    (n : ℕ) (T : (a : V) → (π.Incident a → Fin n) → ℝ) (φ0 : E → Fin n) (c : V)
    [inst : Fintype (π.Incident c)] :
    ∑ φ ∈ P φ0 (Finset.univ.filter (fun e => π.src e = c ∨ π.tgt e = c)),
      (|T c (fun s => φ s.val.1)|) ^ 2 = ∑ j : π.Incident c → Fin n, (T c j) ^ 2 := by
  classical
  let S : V → Finset E := fun c => univ.filter (fun e => π.src e = c ∨ π.tgt e = c)
  show ∑ φ ∈ P φ0 (S c), (|T c (fun s => φ s.val.1)|) ^ 2 = _
  refine Finset.sum_bij (fun φ _ => fun s : π.Incident c => φ s.val.1) ?_ ?_ ?_ ?_
  · intro φ _; exact mem_univ _
  · intro φ hφ ψ hψ h
    simp only [P, mem_filter, mem_univ, true_and] at hφ hψ
    funext e
    by_cases he : e ∈ S c
    · simp only [S, mem_filter, mem_univ, true_and] at he
      by_cases hs : π.src e = c
      · have := congrFun h ⟨(e, true), by simpa using hs⟩
        simpa using this
      · have ht : π.tgt e = c := he.resolve_left hs
        have := congrFun h ⟨(e, false), by simpa using ht⟩
        simpa using this
    · rw [hφ e he, hψ e he]
  · intro x _
    refine ⟨fun e => if h : e ∈ S c then
        x (if hs : π.src e = c then ⟨(e, true), by simpa using hs⟩
           else ⟨(e, false), by
             have := (by simpa [S] using h : π.src e = c ∨ π.tgt e = c)
             simpa using this.resolve_left hs⟩) else φ0 e, ?_, ?_⟩
    · simp only [P, mem_filter, mem_univ, true_and]
      intro e he; simp [he]
    · funext s
      obtain ⟨⟨e, b⟩, hs⟩ := s
      have hmem : e ∈ S c := by
        cases b <;> simp_all [S]
      cases b
      · have ht : π.tgt e = c := by simpa using hs
        have hsrc : ¬ π.src e = c := fun h => hπ e (h.trans ht.symm)
        simp [hmem, hsrc]
      · have hsrc : π.src e = c := by simpa using hs
        simp [hmem, hsrc]
  · intro φ _
    simp only [sq_abs]

open FinnerAux in
theorem lemma_B_3 {V E : Type} [Fintype V] [Fintype E]
    (π : Network V E) (hπ : ∀ e, π.src e ≠ π.tgt e) (n : ℕ)
    (T : (a : V) → (π.Incident a → Fin n) → ℝ) (hT : π.symmetric n T) :
    |π.value n T| ≤ π.normProduct n T := by
  classical
  have hnn : 0 ≤ π.normProduct n T := by
    unfold Network.normProduct
    exact Finset.prod_nonneg fun a _ => Real.sqrt_nonneg _
  by_cases hne : Nonempty (E → Fin n)
  swap
  · have : IsEmpty (E → Fin n) := not_nonempty_iff.mp hne
    have h0 : π.value n T = 0 := by
      unfold Network.value
      simp
    rw [h0]; simpa using hnn
  obtain ⟨φ0⟩ := hne
  let S : V → Finset E := fun c => univ.filter (fun e => π.src e = c ∨ π.tgt e = c)
  let f : V → (E → Fin n) → ℝ := fun c φ => |T c (fun s => φ s.val.1)|
  have hP : P φ0 (univ : Finset E) = univ := by
    ext φ; simp [P]
  have main := finner φ0 (univ : Finset E) S f (fun c φ => abs_nonneg _)
    (fun c => Finset.subset_univ _)
    (by
      intro c φ ψ h
      simp only [f]
      congr 2
      funext s
      apply h
      have := s.2
      simp only [S, mem_filter, mem_univ, true_and]
      by_cases hb : s.val.2
      · left; simpa [hb] using this
      · right; simpa [hb] using this)
    (by
      intro e _
      refine ⟨π.src e, π.tgt e, hπ e, ?_, ?_, ?_⟩
      · simp [S]
      · simp [S]
      · intro c hc
        simpa [S, eq_comm] using hc)
  rw [hP] at main
  have h1 : |π.value n T| ≤ ∑ φ : E → Fin n, ∏ c, f c φ := by
    unfold Network.value
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.abs_prod]
  refine h1.trans (main.trans (le_of_eq ?_))
  unfold Network.normProduct
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold frobenius
  congr 1
  exact bij_sum π hπ n T φ0 c (inst := _)

end GaussPolyReg.Approx

open GaussPolyReg.Approx in
theorem solution {V E : Type} [Fintype V] [Fintype E]
    (π : Network V E) (hπ : ∀ e, π.src e ≠ π.tgt e) (n : ℕ)
    (T : (a : V) → (π.Incident a → Fin n) → ℝ) (hT : π.symmetric n T) :
    |π.value n T| ≤ π.normProduct n T := lemma_B_3 π hπ n T hT
