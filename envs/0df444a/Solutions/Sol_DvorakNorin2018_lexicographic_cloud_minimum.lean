-- Prove2me | solution 1 for DvorakNorin2018.lexicographic_cloud_minimum
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T17:38:02.497065+00:00
-- url     : https://prove2.me/submissions/acc28178-29ab-4ed3-966a-119c71937985

import Definitions.Def_DvorakNorin2018_CloudNormalization
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.TameCloud
lemma total_at_sinks {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V} (hp : Cloud G W α p) :
    total p = ∑ v ∈ W, congestion p v := by
  have hc : (∑ v ∈ Wᶜ, p.1 v) + (∑ v ∈ Wᶜ, incoming p v) =
      ∑ v ∈ Wᶜ, ∑ u, p.2 (v,u) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv => hp.conserve v (Finset.mem_compl.mp hv))
  have hz : (∑ v ∈ W, ∑ u, p.2 (v,u)) = 0 :=
    Finset.sum_eq_zero (fun v hv => Finset.sum_eq_zero (fun u _ => hp.sinks v hv u))
  have hall : (∑ v, incoming p v) = ∑ v, ∑ u, p.2 (v,u) := by
    unfold incoming; exact Finset.sum_comm
  have h₁ := Finset.sum_add_sum_compl W (fun v => p.1 v)
  have h₂ := Finset.sum_add_sum_compl W (incoming p)
  have h₃ := Finset.sum_add_sum_compl W (fun v => ∑ u, p.2 (v,u))
  unfold total congestion
  rw [Finset.sum_add_distrib]
  linarith

/- The whole α≤1 branch of Lemma 6, preserving the supply exactly. -/
theorem normalize_small_congestion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (p : Data V) (hp : Cloud G W α p) :
    ∃ q : Data V, Cloud G W α q ∧ Tame W α q ∧ total q = total p := by
  classical
  let q : Data V := (fun v => if v ∈ W then congestion p v else 0, fun _ => 0)
  have hn : ∀ v, 0 ≤ congestion p v := fun v => add_nonneg (hp.supply v).1
    (Finset.sum_nonneg (fun u _ => hp.flow (u,v)))
  have hqc : ∀ v, congestion q v = if v ∈ W then congestion p v else 0 := by
    intro v; simp [congestion,incoming,q]
  have hcloud : Cloud G W α q := by
    refine ⟨?_,fun _ => le_rfl,fun _ _ _ => rfl,fun _ _ _ => rfl,?_,?_⟩
    · intro v
      change 0 ≤ (if v ∈ W then congestion p v else 0) ∧
        (if v ∈ W then congestion p v else 0) ≤ 1
      by_cases hv : v ∈ W <;> simp only [hv,ite_true,ite_false]
      · exact ⟨hn v,(hp.bound v).trans hα1⟩
      · exact ⟨le_rfl,zero_le_one⟩
    · intro v hv; simp [hqc,hv,q]
    · intro v; rw [hqc]; split_ifs
      · exact hp.bound v
      · exact hα
  refine ⟨q,hcloud,?_,?_⟩
  · refine ⟨fun _ _ _ => rfl,?_,?_⟩
    · intro z _ u v _ _ hpos _; exact False.elim ((lt_irrefl 0) hpos)
    · intro _
      refine ⟨fun _ => rfl,?_⟩
      intro v
      by_cases hv : v ∈ W
      · simp only [hv,iff_true]
        by_cases hsat : q.1 v = 1
        · exact Or.inl hsat
        · exact Or.inr ⟨lt_of_le_of_ne (hcloud.supply v).2 hsat,Or.inr hv⟩
      · have hg : q.1 v = 0 := by simp [q,hv]
        simp [Hungry,hg,hqc,hv]
  · unfold total
    simp only [q]
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun v => v ∈ W)) = W := by ext v; simp
    rw [hf]
    exact (total_at_sinks hp).symm

lemma flow_le_congestion {V : Type} [Fintype V] {G : SimpleGraph V} {W : Finset V}
    {α : ℝ} {p : Data V} (hp : Cloud G W α p) (u v : V) : p.2 (u,v) ≤ α := by
  have hi : p.2 (u,v) ≤ incoming p v := Finset.single_le_sum
    (fun x _ => hp.flow (x,v)) (Finset.mem_univ u)
  have hs := (hp.supply v).1
  have hb := hp.bound v
  dsimp [congestion] at hb
  linarith

/- Compactness gives the actual primary minimizer, with supply fixed exactly. -/
theorem exists_minimum_volume {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ)
    (p : Data V) (hp : Cloud G W α p) (ht : total p = s) :
    ∃ q : Data V, Cloud G W α q ∧ total q = s ∧
      ∀ r : Data V, Cloud G W α r → total r = s → volume q ≤ volume r := by
  classical
  let K : Set (Data V) := {q | Cloud G W α q ∧ total q = s}
  have cv (v : V) : Continuous (fun q : Data V => q.1 v) := by fun_prop
  have cf (a : V × V) : Continuous (fun q : Data V => q.2 a) := by fun_prop
  have cc (v : V) : Continuous (fun q : Data V => congestion q v) := by
    unfold congestion incoming; fun_prop
  have ct : Continuous (fun q : Data V => total q) := by unfold total; fun_prop
  have hclosed : IsClosed K := by
    have h₁ : IsClosed {q : Data V | ∀ v, 0 ≤ q.1 v ∧ q.1 v ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun v => (isClosed_le continuous_const (cv v)).inter
        (isClosed_le (cv v) continuous_const))
    have h₂ : IsClosed {q : Data V | ∀ a, 0 ≤ q.2 a} := by
      simp only [Set.ofPred_forall]; exact isClosed_iInter (fun a => isClosed_le continuous_const (cf a))
    have h₃ : IsClosed {q : Data V | ∀ u v, ¬ G.Adj u v → q.2 (u,v) = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun u => isClosed_iInter (fun v => isClosed_iInter
        (fun _ => isClosed_eq (cf (u,v)) continuous_const)))
    have h₄ : IsClosed {q : Data V | ∀ u ∈ W, ∀ v, q.2 (u,v) = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun u => isClosed_iInter (fun _ => isClosed_iInter
        (fun v => isClosed_eq (cf (u,v)) continuous_const)))
    have h₅ : IsClosed {q : Data V | ∀ v ∉ W, congestion q v = ∑ u, q.2 (v,u)} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun v => isClosed_iInter (fun _ => isClosed_eq (cc v) (by fun_prop)))
    have h₆ : IsClosed {q : Data V | ∀ v, congestion q v ≤ α} := by
      simp only [Set.ofPred_forall]; exact isClosed_iInter (fun v => isClosed_le (cc v) continuous_const)
    have heq : K = {q | ∀ v, 0 ≤ q.1 v ∧ q.1 v ≤ 1} ∩
        ({q | ∀ a, 0 ≤ q.2 a} ∩ ({q | ∀ u v, ¬ G.Adj u v → q.2 (u,v) = 0} ∩
        ({q | ∀ u ∈ W, ∀ v, q.2 (u,v) = 0} ∩
        ({q | ∀ v ∉ W, congestion q v = ∑ u, q.2 (v,u)} ∩
        ({q | ∀ v, congestion q v ≤ α} ∩ {q | total q = s}))))) := by
      ext q
      simp only [K,Set.mem_setOf_eq,Set.mem_inter_iff]
      constructor
      · rintro ⟨hq,hs⟩; exact ⟨hq.supply,hq.flow,hq.support,hq.sinks,hq.conserve,hq.bound,hs⟩
      · rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆,hs⟩; exact ⟨⟨h₁,h₂,h₃,h₄,h₅,h₆⟩,hs⟩
    rw [heq]
    exact h₁.inter (h₂.inter (h₃.inter (h₄.inter (h₅.inter (h₆.inter (isClosed_eq ct continuous_const))))))
  have hbox : IsCompact ((Set.pi Set.univ (fun _ : V => Set.Icc (0 : ℝ) 1)) ×ˢ
      Set.pi Set.univ (fun _ : V × V => Set.Icc (0 : ℝ) α)) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hsub : K ⊆ (Set.pi Set.univ (fun _ : V => Set.Icc (0 : ℝ) 1)) ×ˢ
      Set.pi Set.univ (fun _ : V × V => Set.Icc (0 : ℝ) α) := by
    intro q hq
    exact ⟨fun v _ => (hq.1.supply v),fun a _ => ⟨hq.1.flow a,flow_le_congestion hq.1 a.1 a.2⟩⟩
  have hk : IsCompact K := hbox.of_isClosed_subset hclosed hsub
  have hv : Continuous (fun q : Data V => volume q) := by unfold volume; fun_prop
  obtain ⟨q,hq,hmin⟩ := hk.exists_isMinOn ⟨p,hp,ht⟩ hv.continuousOn
  exact ⟨q,hq.1,hq.2,fun r hr hs => hmin ⟨hr,hs⟩⟩

theorem exists_lex_minimum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ)
    (p : Data V) (hp : Cloud G W α p) (ht : total p = s) :
    ∃ q : Data V, IsLexMinimum G W α s q := by
  classical
  obtain ⟨q,hq,htq,hmin⟩ := exists_minimum_volume G W α s p hp ht
  have hex : ∃ k : ℕ, ∃ r : Data V, Cloud G W α r ∧ total r = s ∧
      volume r = volume q ∧ penalty r = k := ⟨penalty q,q,hq,htq,rfl,rfl⟩
  obtain ⟨r,hr,htr,heq,hpen⟩ := Nat.find_spec hex
  refine ⟨r,hr,htr,?_⟩
  intro u hu htu
  refine ⟨heq ▸ hmin u hu htu,?_⟩
  intro hvol
  rw [hpen]
  exact Nat.find_min' hex ⟨u,hu,htu,hvol.trans heq,rfl⟩

/- The remaining finite rerouting property of a lexicographic minimizer. -/
/- Complete source reduction of Lemma 6. The finite rerouting assertion is an
explicit hypothesis; compact minimization and the α≤1 case are proved here. -/
theorem normalization_from_rerouting {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 < α)
    (p : Data V) (hp : Cloud G W α p) (ht : total p = s)
    (reroute : ∀ q : Data V, 1 < α → IsLexMinimum G W α s q → ReroutingConclusion W q) :
    ∃ q : Data V, Cloud G W α q ∧ Tame W α q ∧ total q = s := by
  by_cases hsmall : α ≤ 1
  · obtain ⟨q,hq,hqt,heq⟩ := normalize_small_congestion G W α hα.le hsmall p hp
    exact ⟨q,hq,hqt,heq.trans ht⟩
  · obtain ⟨q,hq⟩ := exists_lex_minimum G W α s p hp ht
    have hr := reroute q (lt_of_not_ge hsmall) hq
    exact ⟨q,hq.1,⟨hr.1,hr.2,fun h => False.elim (hsmall h)⟩,hq.2.1⟩
end StableMSR.Recovery.TameCloud
open StableMSR.Recovery.TameCloud
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ)
    (p : Data V) (hp : Cloud G W α p) (ht : total p = s) :
    ∃ q : Data V, IsLexMinimum G W α s q := by
  exact exists_lex_minimum G W α s p hp ht
